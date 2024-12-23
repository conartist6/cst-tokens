import { buildDependentLanguages } from '@bablr/helpers/grammar';
import { facades, actuals } from './facades.js';
import { getPrototypeOf } from '@bablr/helpers/object';
import { reifyExpressionShallow } from '@bablr/agast-vm-helpers';

export const ContextFacade = class BABLRContextFacade {
  constructor(actual) {
    facades.set(actual, this);
  }

  get languages() {
    return actuals.get(this).languages;
  }

  get grammars() {
    return actuals.get(this).grammars;
  }

  get productionEnhancer() {
    return actuals.get(this).productionEnhancer;
  }

  getCooked(node) {
    return actuals.get(this).agast.getCooked(actuals.get(node));
  }

  unbox(value) {
    return actuals.get(this).unbox(value);
  }
};

export const Context = class BABLRContext {
  static from(language, productionEnhancer) {
    return new Context(buildDependentLanguages(language), productionEnhancer);
  }

  constructor(languages, productionEnhancer) {
    this.languages = languages;
    this.productionEnhancer = productionEnhancer;

    this.unboxedValues = new WeakMap();

    this.grammars = new WeakMap();
    this.facade = new ContextFacade(this);

    for (const { 1: language } of this.languages) {
      let { prototype } = language.grammar;
      while (prototype && prototype !== Object.prototype) {
        prototype = getPrototypeOf(prototype);
      }
      this.grammars.set(language, new language.grammar());
    }
  }

  unbox(value) {
    const { unboxedValues } = this;
    if (!unboxedValues.has(value)) {
      unboxedValues.set(value, reifyExpressionShallow(value));
    }

    return unboxedValues.get(value);
  }
};
