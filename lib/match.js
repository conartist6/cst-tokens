import { agast } from '@bablr/agast-vm';
import { resolveLanguage } from '@bablr/helpers/grammar';
import { getStreamIterator } from '@bablr/agast-helpers/stream';
import { WeakStackFrame } from '@bablr/weak-stack';

import { get, PathResolver, TagPath } from '@bablr/agast-helpers/path';
import { createPassthroughStrategy } from '@bablr/agast-vm-strategy-passthrough';

import { facades, actuals } from './facades.js';
import { buildGapTag, buildReferenceTag, mergeReferences } from '@bablr/agast-helpers/tree';
import * as btree from '@bablr/agast-helpers/btree';
import { effectsFor, shouldBranch } from '@bablr/agast-vm-helpers';
import { CloseNodeTag, EmbeddedNode, GapTag, OpenNodeTag } from '@bablr/agast-helpers/symbols';

const nodeTopType = Symbol.for('@bablr/node');

class Pump {
  constructor() {
    this.held = null;
  }

  queue(value) {
    this.held = value;
  }

  next() {
    const { held } = this;
    if (!held) throw new Error();
    this.held = null;
    return { done: false, value: held };
  }

  [Symbol.iterator]() {
    return this;
  }
}

export class MatchFacade {
  constructor(match) {
    facades.set(match, this);
  }

  get language() {
    return actuals.get(this).language;
  }

  get matcher() {
    return actuals.get(this).matcher;
  }

  get mergedReference() {
    return actuals.get(this).mergedReference;
  }

  get propertyMatcher() {
    return actuals.get(this).propertyMatcher;
  }

  get depth() {
    return actuals.get(this).depth;
  }

  get path() {
    return actuals.get(this).path;
  }

  get pathDepth() {
    return actuals.get(this).depths.path;
  }

  get pathName() {
    return actuals.get(this).pathName;
  }

  get pathParent() {
    return actuals.get(this).pathParent;
  }

  get node() {
    return actuals.get(this).node;
  }

  get type() {
    return actuals.get(this).type;
  }

  get isNode() {
    return actuals.get(this).isNode;
  }

  get captured() {
    return actuals.get(this).captured;
  }

  get range() {
    return actuals.get(this).range;
  }

  get effects() {
    return actuals.get(this).effects;
  }

  get parent() {
    return facades.get(actuals.get(this).parent);
  }

  get grammar() {
    return actuals.get(this).grammar;
  }

  get state() {
    return facades.get(actuals.get(this).state);
  }

  get s() {
    return facades.get(actuals.get(this).s);
  }

  get rangePrevious() {
    return actuals.get(this).rangePrevious;
  }

  get rangePreviousIndex() {
    return actuals.get(this).rangePreviousIndex;
  }

  get rangeInitial() {
    return actuals.get(this).rangeInitial;
  }

  get rangeFinal() {
    return actuals.get(this).rangeFinal;
  }

  get rangeFinalIndex() {
    return actuals.get(this).rangeFinalIndex;
  }

  ancestors(...args) {
    return actuals.get(this).ancestors(...args);
  }
}

export class Match extends WeakStackFrame {
  constructor(parent, context, language, state, matcher, effects) {
    if (!context || !language || !state) {
      throw new Error('Invalid arguments to Match constructor');
    }

    super(parent);

    this.context = context;
    this.language = language;
    this.state = state;
    this.propertyMatcher = matcher;
    this.effects = effects;

    this.rangePreviousIndex = null;
    this.rangeFinalIndex = null;

    if (this.isNode || !parent || shouldBranch(effects)) {
      this.agastPump = new Pump();
      this.expressionsPump = new Pump();
      this.agastState = null;
      this.agast = getStreamIterator(
        agast(
          (ctx, s) => {
            this.agastState = s;
            return createPassthroughStrategy(this.agastPump)(ctx, s);
          },
          { expressions: this.expressionsPump },
        ),
      );

      if (shouldBranch(effects) && !this.isNode) {
        let resolver = new PathResolver();
        for (let tag of btree.traverse(parent.agastState.node.children)) {
          if (tag.type === GapTag) {
            let { name, isArray, flags } = resolver.reference.value;
            const resolvedPath = buildReferenceTag(name, isArray, flags, resolver.counters[name]);
            const expr = get(resolvedPath, parent.agastState.node);
            this.expressionsPump.queue(expr);
          } else if (tag.type === EmbeddedNode) {
            this.expressionsPump.queue(tag.value);
            tag = buildGapTag();
          }

          resolver.advance(tag);

          this.agastPump.queue(tag);
          this.agast.next();
        }
      }
    } else {
      this.agastPump = parent.agastPump;
      this.expressionsPump = parent.expressionsPump;
      this.agastState = parent.agastState;
      this.agast = parent.agast;
    }

    this.path = this.agastState.path || this.agastState.result.path;

    if (!this.path) throw new Error();

    new MatchFacade(this);
  }

  static from(context, language, state, matcher, options = {}) {
    return Match.create(context, language, state, matcher, effectsFor('eat'), options);
  }

  get matcher() {
    return this.propertyMatcher?.nodeMatcher.open;
  }

  get mergedReference() {
    let ref = buildReferenceTag('.');

    let first = true;
    for (const m of this.ancestors(true)) {
      if (m.isNode && !first) break;
      if (m.propertyMatcher.refMatcher) {
        const { name, isArray, flags } = m.propertyMatcher.refMatcher;
        const parentRef = buildReferenceTag(name, isArray, flags);
        ref = ['#', '@'].includes(ref.value.name) ? ref : mergeReferences(ref, parentRef);
      }
      first = false;
    }

    return ref;
  }

  get pathName() {
    return this.mergedReference.value.name;
  }

  get node() {
    return this.path.node;
  }

  get pathParent() {
    let m = this;
    let { path } = this;

    while (m && m.path.node === path.node) {
      m = m.parent;
    }
    return m;
  }

  get parentPath() {
    return this.pathParent?.path;
  }

  get ctx() {
    return this.context;
  }

  get grammar() {
    return this.context.grammars.get(this.language);
  }

  get s() {
    return this.state;
  }

  get type() {
    return this.matcher?.type || null;
  }

  get flags() {
    return this.matcher?.flags;
  }

  get captured() {
    return !this.rangePrevious || !!this.rangeFinal;
  }

  get allowEmpty() {
    return this.grammar.emptyables.has(this.type);
  }

  get rangePrevious() {
    const path = !this.isNode || !this.parent ? this.path : this.parent?.path;

    return this.rangePreviousIndex == null ? null : new TagPath(path, this.rangePreviousIndex);
  }

  get rangeFinal() {
    const path = !this.parent ? this.path : this.parent.path;

    return this.rangeFinalIndex == null ? null : new TagPath(path, this.rangeFinalIndex);
  }

  get rangeInitial() {
    const { path, rangePrevious, isNode } = this;
    if (rangePrevious && isNode) {
      return new TagPath(path, 0);
    } else {
      return rangePrevious?.nextSibling;
    }
  }

  get range() {
    const { rangeInitial, rangeFinal } = this;
    return rangeInitial === null ? null : [rangeInitial, rangeFinal];
  }

  get isNode() {
    const { grammar, type } = this;
    return grammar.covers?.get(nodeTopType).has(type);
  }

  get isCover() {
    const { grammar, type } = this;
    return grammar.covers?.has(type);
  }

  advance(tag) {
    let m =
      this.state.node &&
      this.state.node !== this.node &&
      ![OpenNodeTag, CloseNodeTag].includes(tag.type) &&
      this.parent
        ? this.parent
        : this;
    m.agastPump.queue(tag);
    m.agast.next();

    this.state.result = TagPath.from(m.path, -1);
  }

  add(node) {
    this.expressionsPump.queue(node);
    this.agastPump.queue(buildGapTag());
    this.agast.next();
  }

  startFrame(state, propertyMatcher, effects, options = {}) {
    let { context } = this;
    const { nodeMatcher } = propertyMatcher;

    const language = resolveLanguage(context, this.language, nodeMatcher.open.language);

    if (!language) {
      throw new Error(`Unknown language ${nodeMatcher.open.language.join('.')}`);
    }

    return this.push(context, language, state, propertyMatcher, effects, options);
  }

  endFrame() {
    let m = this.parent;

    if (m && !this.isNode) {
      m.path = this.path;
    }

    return m;
  }
}
