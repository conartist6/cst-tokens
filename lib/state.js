import emptyStack from '@iter-tools/imm-stack';
import { WeakStackFrame } from '@bablr/weak-stack';
import { getCooked } from '@bablr/agast-helpers/stream';
import { reifyExpression } from '@bablr/agast-vm-helpers';
import { CloseNodeTag, EmbeddedNode, GapTag } from '@bablr/agast-helpers/symbols';
import * as btree from '@bablr/agast-helpers/btree';
import { acceptNode, buildGapTag, buildReferenceTag } from '@bablr/agast-helpers/tree';
import { get, Path, PathResolver, TagPath, updatePath } from '@bablr/agast-helpers/path';
import { match, guardWithPattern } from './utils/pattern.js';
import { facades, actuals } from './facades.js';
import { NodeFacade, buildInternalState, internalStates } from './node.js';

export const nodeStates = new WeakMap();

export const StateFacade = class BABLRStateFacade {
  constructor(state) {
    facades.set(state, this);
  }

  static from(source) {
    return State.from(actuals.get(source));
  }

  get ctx() {
    return actuals.get(this).context;
  }

  get span() {
    return actuals.get(this).span.name;
  }

  get result() {
    return actuals.get(this).result;
  }

  get reference() {
    return actuals.get(this).reference;
  }

  get referenceTagPath() {
    return actuals.get(this).referenceTagPath;
  }

  get holding() {
    return actuals.get(this).holding;
  }

  get path() {
    return actuals.get(this).path;
  }

  get depths() {
    const { path, result } = actuals.get(this).depths;
    return { path, result };
  }

  get node() {
    return NodeFacade.wrap(actuals.get(this).node, this.ctx);
  }

  get parentNode() {
    return NodeFacade.wrap(actuals.get(this).parentNode, this.ctx);
  }

  get source() {
    return facades.get(actuals.get(this).source);
  }

  get depth() {
    return actuals.get(this).depth;
  }

  get status() {
    return actuals.get(this).status;
  }

  get parent() {
    return facades.get(actuals.get(this).parent);
  }

  nodeForPath(path) {
    return actuals.get(this).nodeForPath(path);
  }
};

export const State = class BABLRState extends WeakStackFrame {
  constructor(
    parent,
    source,
    context,
    balanced = emptyStack,
    spans = emptyStack.push({ name: 'Bare' }),
    referenceTagPath = null,
    result = null,
    depths = { path: -1, result: -1 },
    emitted = null,
    held = null,
    node = null,
  ) {
    super(parent);

    if (!source) throw new Error('invalid args to State');

    this.source = source;
    this.context = context;
    this.balanced = balanced;
    this.spans = spans;
    this.referenceTagPath = referenceTagPath;
    this.result = result;
    this.depths = depths;
    this.emitted = emitted;
    this.held = held;
    this.node = node;

    this.status = 'active';

    new StateFacade(this);
  }

  static from(source, context) {
    return State.create(source, context);
  }

  get unboundAttributes() {
    return nodeStates.get(this.node).unboundAttributes;
  }

  get guardedSource() {
    const { source, span } = this;
    const { guard } = span;

    return guard ? guardWithPattern(guard, source) : source;
  }

  get span() {
    return this.spans.value;
  }

  get path() {
    throw new Error('not implemented');
  }

  get parentNode() {
    throw new Error('not implemented');
  }

  get holding() {
    return !!this.held;
  }

  get reference() {
    return this.referenceTagPath?.tag;
  }

  get isGap() {
    return this.tag.type === GapTag;
  }

  get speculative() {
    return !!this.parent;
  }

  advance(tag) {
    const { path, agastPump, agast } = internalStates.get(this.node);
    agastPump.queue(tag);
    agast.next();

    this.result = TagPath.from(path, -1);
  }

  guardedMatch(pattern) {
    let { span, source } = this;
    let { guard } = span;

    let pattern_ = pattern;
    if (pattern.type === EmbeddedNode) {
      if (pattern.value.type === Symbol.for('PropertyMatcher')) {
        pattern_ = reifyExpression(pattern.value).nodeMatcher.open;
      } else {
        pattern_ = reifyExpression(pattern.value);
      }
    }

    if (
      span.type === 'Lexical' &&
      pattern.type === EmbeddedNode &&
      pattern.value.type === Symbol.for('PropertyMatcher') &&
      (pattern_.flags.token
        ? pattern_.attributes.balancer || pattern_.attributes.balanced
        : pattern_.attributes?.balancer)
    ) {
      // also check that the open node starts a lexical span?
      guard = null;
    }

    if (pattern_?.intrinsicValue) {
      // if (pattern.type === OpenNodeTag) {

      //   // TODO differntiate better between self-closing tags and matchers
      //   pattern = pattern.value;
      // }

      pattern_ = pattern_.intrinsicValue || getCooked(pattern_.children);

      if (pattern_.type === Symbol.for('String')) {
        pattern_ = reifyExpression(pattern_);
      }
    }

    return match(pattern_, guard ? guardWithPattern(guard, source) : source);
  }

  match(pattern) {
    return match(pattern, this.source);
  }

  branch() {
    const baseState = this;
    let {
      source,
      context,
      balanced,
      spans,
      result,
      depths,
      referenceTagPath,
      emitted,
      held,
      node,
    } = baseState;

    let resolver = new PathResolver();

    const internalState = buildInternalState();

    for (let tag of btree.traverse(node.children)) {
      if (tag.type === GapTag) {
        let { name, isArray, flags } = resolver.reference.value;
        const resolvedPath = buildReferenceTag(name, isArray, flags, resolver.counters[name]);
        const expr = get(resolvedPath, node);
        internalState.expressionsPump.queue(expr);
      } else if (tag.type === EmbeddedNode) {
        internalState.expressionsPump.queue(tag.value);
        tag = buildGapTag();
      }

      resolver.advance(tag);

      internalState.agastPump.queue(tag);
      internalState.agast.next();
    }

    const newNode = internalState.agastState.node;
    const nodeState = nodeStates.get(node);
    let newEmitted, newResult;

    if (emitted.path.node === node) {
      newEmitted = TagPath.from(Path.from(newNode), emitted.childrenIndex);
    } else {
      newEmitted = emitted;
    }

    if (result.path.node === node) {
      newResult = TagPath.from(Path.from(newNode), result.childrenIndex);
    } else {
      newResult = result;
    }

    nodeStates.set(newNode, { ...nodeState });
    internalStates.set(newNode, internalState);

    const child = this.push(
      source.branch(),
      context,
      balanced,
      spans,
      referenceTagPath,
      newResult,
      depths,
      newEmitted,
      held,
      newNode,
    );

    return child;
  }

  accept() {
    const accepted = this;

    this.status = 'accepted';

    const { parent } = this;

    if (!parent) {
      throw new Error('accepted the root state');
    }

    parent.spans = accepted.spans;
    parent.balanced = accepted.balanced;
    parent.referenceTagPath = accepted.referenceTagPath;
    parent.held = accepted.held;
    parent.depths = accepted.depths;

    if (parent.depths.path === accepted.depths.path) {
      const parentChildren = parent.node.children;
      parent.node.children = parentChildren;

      const internalState = internalStates.get(parent.node);
      const { path: parentPath } = internalState;
      for (let i = btree.getSum(parentChildren); i < btree.getSum(accepted.node.children); i++) {
        let tag = btree.getAt(i, accepted.node.children);

        if (tag.type === GapTag) {
          let reference = btree.getAt(i - 1, accepted.node.children);
          let { name, isArray, flags } = reference.value;
          const resolvedPath = buildReferenceTag(
            name,
            isArray,
            flags,
            btree.getSum(parentPath.node.properties[name]),
          );
          const expr = get(resolvedPath, accepted.node);
          internalState.expressionsPump.queue(expr);
        } else if (tag.type === EmbeddedNode) {
          internalState.expressionsPump.queue(tag.value);
          tag = buildGapTag();
        }

        internalState.agastPump.queue(tag);
        internalState.agast.next();

        updatePath(parentPath, tag);
      }
    }

    if (
      parent.depths.result ===
      accepted.depths.result + (accepted.result.type === CloseNodeTag ? 0 : 1)
    ) {
      parent.result = new TagPath(parent.result.path, accepted.result.childrenIndex);
    } else {
      parent.result = accepted.result;
    }

    parent.emitted = accepted.emitted;

    nodeStates.set(parent.node, nodeStates.get(accepted.node));

    parent.source.accept(accepted.source);

    return parent;
  }

  reject() {
    const rejectedState = this;
    const { parent } = rejectedState;

    if (this.status === 'rejected') {
      return parent;
    }

    if (this.status !== 'active') throw new Error();

    this.status = 'rejected';

    if (!parent) throw new Error('rejected root state');

    rejectedState.source.reject();

    return parent;
  }
};
