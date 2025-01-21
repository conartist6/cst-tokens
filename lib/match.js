import { resolveLanguage } from '@bablr/helpers/grammar';
import { WeakStackFrame } from '@bablr/weak-stack';

import { allTagsFor, get, TagPath, tagPathsAreEqual } from '@bablr/agast-helpers/path';
import { isEmpty } from '@bablr/agast-helpers/stream';
import * as btree from '@bablr/agast-helpers/btree';
import {
  buildGapTag,
  buildReferenceTag,
  mergeReferences,
  streamFromTree,
} from '@bablr/agast-helpers/tree';
import { effectsFor, shouldBranch } from '@bablr/agast-vm-helpers';
import { buildInternalState, internalStates } from './node.js';

import { facades, actuals } from './facades.js';
import {
  CloseNodeTag,
  EmbeddedNode,
  GapTag,
  OpenNodeTag,
  ReferenceTag,
} from '@bablr/agast-helpers/symbols';
import { nodeStates } from './state.js';

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

  get fragmentNode() {
    return actuals.get(this).fragmentNode;
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

    this.rangePreviousIndex = null;
    this.rangeFinalIndex = null;

    let internalState;
    let { isNode } = this;

    if (isNode || !parent) {
      internalState = buildInternalState();
    } else {
      const { agastPump, expressionsPump, agastState, agast } = internalStates.get(parent.node);
      internalState = { agastPump, expressionsPump, agastState, agast, path: agastState.path };
    }

    this.node = internalState.path.node;
    this.fragmentNode = null; // why do it this way?

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
    return agastState.path || agastState.resultPath.path;
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

    if (this.isNode && this.rangePrevious.tag.type === ReferenceTag) {
      throw new Error();
    }
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

  endFrame() {
    const finishedMatch = this;
    const m = finishedMatch.parent;
    let finishedState = finishedMatch.state;

    if (!m) return m;

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

    return m;
  }

  *emit() {
    let { state } = this;

    if (!state.depth) {
      let { node, emitted } = state;

      let { path } = internalStates.get(node);

      let emittable = emitted
        ? emitted.nextSibling
        : btree.getSum(path)
        ? new TagPath(path, 0)
        : null;

      // two basic cases:
      //   emitted can move
      //   emitted cannot move

      while (
        emittable &&
        !(
          emittable.tag.type === OpenNodeTag &&
          emittable.tag.value.type &&
          nodeStates.get(emittable.path.node).unboundAttributes?.size
        )
      ) {
        let isntAGapNode = true;
        if (emittable.tag.type === GapTag && isntAGapNode) {
          let ref = emittable.previousSibling;
          let resolvedRef = ref.tag;

          if (ref.tag.value.isArray) {
            const { name, flags, isArray } = ref.tag.value;
            resolvedRef = buildReferenceTag(
              name,
              isArray,
              flags,
              ref.path.referenceIndexes[ref.childrenIndex],
            );
          }
          let resolvedNode = get(resolvedRef, emittable.node);

          if (btree.getAt(-1, resolvedNode.children)?.type === CloseNodeTag) {
            yield* streamFromTree(resolvedNode);

            state.emitted = emitted = emitted.nextSibling;
            emittable = emitted.nextSibling;
            if (!emittable) {
              break;
            }
          } else {
            break;
          }
        } else if (emittable.tag.type === EmbeddedNode) {
          let node = emittable.tag.value;
          if (btree.getAt(-1, node.children)?.type === CloseNodeTag) {
            yield* streamFromTree(node);

            state.emitted = emitted = emitted.nextSibling;
            emittable = emitted.nextSibling;
          } else {
            break;
          }
        } else {
          state.emitted = emitted = emittable;

          yield emitted.tag;

          emittable = emitted.nextSibling;
        }
      }
    }
  }
}
