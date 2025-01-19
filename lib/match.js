import { resolveLanguage } from '@bablr/helpers/grammar';
import { WeakStackFrame } from '@bablr/weak-stack';

import { allTagsFor, TagPath } from '@bablr/agast-helpers/path';
import { isEmpty } from '@bablr/agast-helpers/stream';
import * as btree from '@bablr/agast-helpers/btree';
import { buildGapTag, buildReferenceTag, mergeReferences } from '@bablr/agast-helpers/tree';
import { effectsFor, shouldBranch } from '@bablr/agast-vm-helpers';
import { CloseNodeTag, EmbeddedNode, GapTag, OpenNodeTag } from '@bablr/agast-helpers/symbols';
import { buildInternalState, internalStates } from './node.js';
import { nodeStates } from './state.js';

const tagPathsAreEqual = (a, b) => {
  if (a == null || b == null) return b == a;
  return a.path.node === b.path.node && a.childrenIndex === b.childrenIndex;
};

import { facades, actuals } from './facades.js';

const nodeTopType = Symbol.for('@bablr/node');

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
    this.state = shouldBranch(effects) ? state.branch() : state;
    this.propertyMatcher = matcher;
    this.effects = effects;
    this._emitted = parent?.emitted || null;

    this.rangePreviousIndex = null;
    this.rangeFinalIndex = null;

    let internalState;
    let { isNode } = this;

    if (isNode) {
      this._emitted = null;
    }

    if (isNode || !parent) {
      internalState = buildInternalState();
    } else {
      const { agastPump, expressionsPump, agastState, agast } = internalStates.get(parent.node);
      internalState = { agastPump, expressionsPump, agastState, agast, path: agastState.path };
    }

    this.node = internalState.path.node;

    internalStates.set(this.node, internalState);

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

  get path() {
    let { agastState } = internalStates.get(this.fragmentNode || this.node);
    return agastState.path || agastState.result.path;
  }

  get pathParent() {
    let m = this;

    do {
      m = m.parent;
    } while (m && !m.isNode);
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
    return this.rangePreviousIndex == null ? null : new TagPath(this.path, this.rangePreviousIndex);
  }

  setRangePreviousIndex(value) {
    this.rangePreviousIndex = value;
    this.rangePrevious;
  }

  setRangeFinalIndex(value) {
    this.rangeFinalIndex = value;
    this.rangeFinal;
  }

  get rangeFinal() {
    const path = !this.parent ? this.path : this.parent.path;

    return this.rangeFinalIndex == null ? null : new TagPath(path, this.rangeFinalIndex);
  }

  get rangeInitial() {
    const { fragmentNode, rangePrevious, isNode } = this;
    if (rangePrevious && isNode) {
      return new TagPath(internalStates.get(fragmentNode).agastState.path, 0);
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

  get reference() {
    return this.isNode ? this.rangePrevious.nextSibling : null;
  }

  get isCover() {
    const { grammar, type } = this;
    return grammar.covers?.has(type);
  }

  add(node) {
    const { expressionsPump, agastPump, agast } = internalStates.get(this.fragmentNode);
    expressionsPump.queue(node);
    agastPump.queue(buildGapTag());
    agast.next();
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

  get emitted() {
    return this._emitted;
  }

  set emitted(value) {
    if (value.path.node !== this.path.node) throw new Error();
    this._emitted = value;
  }

  endFrame() {
    const finishedMatch = this;
    const m = finishedMatch.parent;
    let finishedState = finishedMatch.state;

    if (finishedState !== m.state) {
      if (
        (!isEmpty(allTagsFor(finishedMatch.range)) || finishedMatch.allowEmpty) &&
        finishedMatch.state.status !== 'rejected'
      ) {
        finishedState.accept();
        finishedMatch.setRangeFinalIndex(btree.getSum(m.fragmentNode.children) - 1);
      } else {
        finishedState.reject();
        finishedMatch.setRangePreviousIndex(null);
      }
    } else {
      finishedMatch.setRangeFinalIndex(btree.getSum((m.fragmentNode || m.node).children) - 1);
    }

    if (!finishedMatch.isNode) {
      m.emitted = finishedMatch.emitted;
    }

    return m;
  }

  get emittable() {
    let leaving = this.state.emitted?.tag.type === CloseNodeTag;

    if (!this.emitted) {
      let { path } = internalStates.get(this.node);
      if (this.isNode && tagPathsAreEqual(this.parent.emittable, this.reference)) {
        return this.reference;
      }

      return btree.getSum(path.node.children) ? new TagPath(path, 0) : null;
    }

    let tagPath = this.emitted;

    for (;;) {
      let isInitialTag = tagPathsAreEqual(tagPath, this.emitted);
      let wasLeaving = leaving;
      leaving = tagPath.tag.type === GapTag ? false : leaving;

      // done
      if (
        !isInitialTag &&
        tagPath.tag.type !== EmbeddedNode &&
        (tagPath.tag.type !== GapTag || this.path.node.type === Symbol.for('@bablr/gap'))
      ) {
        return tagPath;
      }

      // in
      if (tagPath.tag.type === EmbeddedNode && !wasLeaving) {
        let { path } = internalStates.get(tagPath.tag.value).agastState;
        tagPath = new TagPath(path, 0);
        continue;
      }

      // in
      if (
        tagPath.tag.type === GapTag &&
        !wasLeaving &&
        tagPath.path.node.type !== Symbol.for('@bablr/gap')
      ) {
        let { path } = internalStates.get(tagPath.node);
        let refTag = btree.getAt(tagPath.childrenIndex - 1, path.node.children);
        let { referenceIndexes } = path;

        if (
          !(refTag.value.name === '#' || refTag.value.name === '@') &&
          (!refTag.value.isArray || referenceIndexes[tagPath.childrenIndex - 1] != null)
        ) {
          let { name, isArray, flags } = refTag.value;
          let resolvedReference = null;
          if (isArray) {
            let index = referenceIndexes[tagPath.childrenIndex - 1];
            resolvedReference =
              index === -1 ? null : buildReferenceTag(name, index != null, flags, index);
          } else {
            resolvedReference = refTag;
          }

          if (resolvedReference) {
            if (!path.get(resolvedReference)) {
              return null;
            }
            tagPath = new TagPath(path.get(resolvedReference), 0);
            continue;
          }
        }
      }

      // over
      if (tagPath.nextSibling) {
        tagPath = tagPath.nextSibling;
        continue;
      }

      // out
      if (
        tagPath.path.referenceIndex != null &&
        tagPath.path.referenceIndex + 1 < btree.getSum(tagPath.path.outer.children)
      ) {
        tagPath = new TagPath(
          internalStates.get(tagPath.path.outer).path,
          tagPath.path.referenceIndex + 1,
        );

        leaving = true;
        continue;
      }

      return null;
    }
  }

  *emit() {
    let { state } = this;

    if (!state.depth) {
      let { emittable } = this;

      while (
        emittable &&
        !(
          emittable.child.type === OpenNodeTag &&
          emittable.child.value.type &&
          nodeStates.get(emittable.path.node).unboundAttributes?.size
        )
      ) {
        yield emittable.child;

        m.emitted = emittable;
        m.state.emitted = emittable;

        if (tagPathsAreEqual(m.emitted, m.parent?.emitted?.nextSibling)) {
          m.parent.emitted = m.emitted;
        }

        ({ emittable } = m);
      }
    }
  }
}
