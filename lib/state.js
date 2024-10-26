import emptyStack from '@iter-tools/imm-stack';
import { WeakStackFrame } from '@bablr/weak-stack';
import { getCooked } from '@bablr/agast-helpers/stream';
import { match, guardWithPattern } from './utils/pattern.js';
import { facades, actuals } from './facades.js';
import { reifyExpression } from '@bablr/agast-vm-helpers';
import { EmbeddedNode, GapTag } from '@bablr/agast-helpers/symbols';
import { NodeFacade } from './node.js';

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

  get holding() {
    return actuals.get(this).holding;
  }

  get path() {
    return actuals.get(this).path;
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

  nodeForPath(path) {
    return NodeFacade.wrap(actuals.get(this).nodeForPath(path), this.ctx);
  }

  pathForTag(tag) {
    return actuals.get(this).pathForTag(tag);
  }

  nodeForTag(tag) {
    return NodeFacade.wrap(actuals.get(this).nodeForTag(tag), this.ctx);
  }
};

export const State = class BABLRState extends WeakStackFrame {
  constructor(
    source,
    agast,
    context,
    balanced = emptyStack,
    spans = emptyStack.push({ name: 'Bare' }),
  ) {
    super();

    if (!source || !agast) throw new Error('invalid args to State');

    this.source = source;
    this.agast = agast;
    this.context = context;
    this.balanced = balanced;
    this.spans = spans;

    this.status = 'active';

    new StateFacade(this);
  }

  static from(source, agast, context) {
    return State.create(source, agast, context);
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
    return this.agast.path;
  }

  get node() {
    return this.agast.node;
  }

  get parentNode() {
    return this.agast.parentNode;
  }

  get holding() {
    return this.agast.holding;
  }

  get result() {
    return this.agast.result;
  }

  get isGap() {
    return this.tag.type === GapTag;
  }

  get speculative() {
    return !!this.parent;
  }

  nodeForPath(path) {
    return this.agast.nodeForPath(path);
  }

  pathForTag(tag) {
    return this.agast.pathForTag(tag);
  }

  nodeForTag(tag) {
    return this.agast.nodeForTag(tag);
  }

  guardedMatch(pattern) {
    let { span, spans, source, node } = this;
    let { guard } = span;

    if (pattern.type === EmbeddedNode) {
      pattern = reifyExpression(pattern.value);
    }

    if (
      span.type === 'Lexical' &&
      (node.flags.token
        ? node.attributes.balancer || node.attributes.balanced
        : pattern.attributes?.balancer)
    ) {
      // also check that the open node starts a lexical span?
      guard = null;
    }

    if (pattern?.intrinsicValue) {
      // if (pattern.type === OpenNodeTag) {

      //   // TODO differntiate better between self-closing tags and matchers
      //   pattern = pattern.value;
      // }

      pattern = pattern.intrinsicValue || getCooked(pattern.children);

      if (pattern.type === 'String') {
        pattern = reifyExpression(pattern);
      }
    }

    return match(pattern, guard ? guardWithPattern(guard, source) : source);
  }
};
