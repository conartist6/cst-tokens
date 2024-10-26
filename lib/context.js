import { buildDependentLanguages } from '@bablr/helpers/grammar';
import { facades, actuals } from './facades.js';
import { getPrototypeOf } from '@bablr/helpers/object';
import { actuals as nodeActuals } from './node.js';

export const ContextFacade = class BABLRContextFacade {
  get languages() {
    return actuals.get(this).languages;
  }

  get grammars() {
    return actuals.get(this).grammars;
  }

  get productionEnhancer() {
    return actuals.get(this).productionEnhancer;
  }

  get agast() {
    return actuals.get(this).agast;
  }

  getPreviousTag(token) {
    return actuals.get(this).agast.getPreviousTag(token);
  }

  allTagsFor(range) {
    return actuals.get(this).agast.allTagsFor(range);
  }

  ownTagsFor(range) {
    return actuals.get(this).agast.ownTagsFor(range);
  }

  getCooked(node) {
    return actuals.get(this).agast.getCooked(actuals.get(node));
  }

  reifyExpression(value) {
    return actuals.get(this).agast.reifyExpression(value);
  }

  sourceTextFor(node) {
    return actuals.get(this).agast.sourceTextFor(nodeActuals.get(node));
  }

  unbox(value) {
    return actuals.get(this).agast.unbox(value);
  }
};

export const Context = class BABLRContext {
  static from(agastContext, language, productionEnhancer) {
    return new Context(agastContext, buildDependentLanguages(language), productionEnhancer);
  }

  constructor(agastContext, languages, productionEnhancer) {
    this.agast = agastContext;
    this.languages = languages;
    this.productionEnhancer = productionEnhancer;

    this.grammars = new WeakMap();
    this.facade = new ContextFacade();

    for (const { 1: language } of this.languages) {
      let { prototype } = language.grammar;
      while (prototype && prototype !== Object.prototype) {
        prototype = getPrototypeOf(prototype);
      }
      this.grammars.set(language, new language.grammar());
    }

    facades.set(this, this.facade);
  }
};
