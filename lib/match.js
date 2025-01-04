import { agast } from '@bablr/agast-vm';
import { resolveLanguage } from '@bablr/helpers/grammar';
import { getStreamIterator, isEmpty } from '@bablr/agast-helpers/stream';
import { WeakStackFrame } from '@bablr/weak-stack';

import { allTagsFor, TagPath } from '@bablr/agast-helpers/path';
import { createPassthroughStrategy } from '@bablr/agast-vm-strategy-passthrough';

import { nodeStates } from './state.js';
import { facades, actuals } from './facades.js';
import { buildGapTag } from '@bablr/agast-helpers/tree';
import { effectsFor } from '@bablr/agast-vm-helpers';

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
  constructor(parent, context, language, state, matcher, effects, options) {
    if (!context || !language || !state) {
      throw new Error('Invalid arguments to Match constructor');
    }

    const { unboundAttributes } = options;

    super(parent);

    this.context = context;
    this.language = language;
    this.state = state;
    this.propertyMatcher = matcher;
    this.effects = effects;

    this.rangePrevious = null;
    this.rangeFinal = null;

    this.agastPump = this.isNode || !parent ? new Pump() : parent.agastPump;
    this.expressionsPump = this.isNode || !parent ? new Pump() : parent.expressionsPump;
    this.agastState = this.isNode || !parent ? null : parent.agastState;
    this.agast =
      this.isNode || !parent
        ? getStreamIterator(
            agast(
              (ctx, s) => {
                this.agastState = s;
                return createPassthroughStrategy(this.agastPump)(ctx, s);
              },
              { expressions: this.expressionsPump },
            ),
          )
        : parent.agast;

    this.path = this.agastState.path || this.agastState.result.path;

    if (!this.path) throw new Error();

    nodeStates.set(this.path.node, {
      unboundAttributes: new Set(unboundAttributes || []),
    });

    new MatchFacade(this);
  }

  static from(context, language, state, matcher, options = {}) {
    return Match.create(context, language, state, matcher, effectsFor('eat'), options);
  }

  get matcher() {
    return this.propertyMatcher?.nodeMatcher.open;
  }

  get pathName() {
    return this.propertyMatcher.refMatcher?.name || '.';
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

  set rangePreviousIndex(value) {
    const { path } = this.parent;

    this.rangePrevious = value && new TagPath(path, value);
  }

  get rangePreviousIndex() {
    return this.rangePrevious?.childrenIndex;
  }

  set rangeFinalIndex(value) {
    const { path } = this.parent;

    this.rangeFinal = value && new TagPath(path, value);
  }

  get rangeFinalIndex() {
    return this.rangeFinal?.childrenIndex;
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
    this.agastPump.queue(tag);
    this.agast.next();

    this.state.result = TagPath.from(this.path, -1);
  }

  add(node) {
    this.expressionsPump.queue(node);
    this.agastPump.queue(buildGapTag());
    this.agast.next();
  }

  startFrame(state, propertyMatcher, effects, options = {}) {
    let { context } = this;
    const { grammars, productionEnhancer } = context;
    const { nodeMatcher } = propertyMatcher;
    const { type } = nodeMatcher.open;

    const language = resolveLanguage(context, this.language, nodeMatcher.open.language);
    const grammar = grammars.get(language);
    const isNode = grammar.covers.get(Symbol.for('@bablr/node')).has(type);

    if (!language) {
      throw new Error(`Unknown language ${nodeMatcher.open.language.join('.')}`);
    }

    return this.push(context, language, state, propertyMatcher, effects, options);
  }

  endFrame() {
    return this.parent;
  }
}
