# Preamble

## File options

First we specify the command line options that should be supplied to the Agda compiler / interpreter when this script is processed. These are supplied in a specially formatted comment block.

In the following code we've set the following options:
* `--without-K` disables Streicher’s K axiom, which we don’t want for univalent mathematics. We'll explain why later.
* `--exact-split` makes Agda to only accept definitions with the equality sign “=” that behave like so-called judgemental or definitional equalities.
* `--safe` disables features that may make Agda inconsistent, such as `--type-in-type`, postulates and more.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}
```

## Module declaration and imports

Every module file must start with a `module` stanza.

```agda
module exercises-week1 where
```

**Note:** the `module-name` must match the base of the file name `module-name.lagda.md`. The extension `.lagda.md` tells Agda that this is a **literate file** written in the markup language [Markdown](https://markdown.org). The contents of the file itself is intended to be a human readable document, with Agda code interspersed throughout and enclosed **fenced code blocks**. These start with \`\`\` or \`\`\`agda on its own line, and end with \`\`\`, also on its own line

Next we import any modules that contain Adga code that this module depends upon.

```agda
open import Agda.Primitive public
```
Here the:

* `open` directive tells Agda that we want to refer to the definitions exported by the imported module using their simple declared names, rather than prefix them with the path `Agda.Primitive.`.
* `public` modifier specifies that the definitions imported by this stanza should be re-exported to any modules that import this one.

# Code

## Standard definitions

This following code sets up the notation for the **universes** `UU i` which are _types of types_ Formally, `UU` is a function which takes as input a **level** `i : Level` and produces `UU i`, the type of types of level at most i. 

To avoid Russell's paradox, the type `UU i` is a type of the next universe level `UU (lsuc i).

**The takeaway:** to declare that "`A` is a type of arbitrary universe level" write `A : UU i` in a context where `i : Level`.

```agda 
UU : (i : Level) → Set (lsuc i)
UU i = Set i
```

## Natural numbers

We define the natural numbers to be an **inductive type** at level `lzero`, the lowest universe level.

```agda 
data ℕ : UU lzero where
    zero-ℕ : ℕ
    succ-ℕ : ℕ → ℕ
```     

In essence, this declaration:

* declares a new type `ℕ` in universe `UU lzero` in in its first line,
* which has a **zero** element `zero-ℕ` specified, given in its second line, and
* specifies that every element `n : ℕ` should have a **successor** `succ-ℕ n : ℕ` in its third line.

Later on we will see how we can build a function which encapsulates the the usual natural number **induction principle** using the **pattern matching** facilities of Agda. We won't do that here, since we haven't yet discussed the general form of data types and the rules that define them, but we will have lots to say about induction in type theory as we go along.

For the moment, we'll just amuse ourselves with some basic exercises: 

**Note:** To insert the natural number symbol ℕ type the character sequence "\\-b-N". Watch what happens at the bottom of the Visual Studio Code as you do for clues on how to insert other mathematical characters. By typing "\\" we enter _unicode input mode_, which allows us to translate the subsequent character sequence into a unicode symbol.

### Exercise 1.1: Define a function to add two natual numbers:

```agda 
add-ℕ : ℕ → ℕ → ℕ
add-ℕ n m = {!   !}
```

**Hint:** pattern match the first parameter `n` and you'll then two cases `n = ℕ-zero` and `n = ℕ-zero n'`for some value `n'`. The first case is easy (0 + m = m) but the second case requires us to **recurse** by computing `add-ℕ n' m` and then returning its successor ((n + 1) + m = (n + m) + 1).

### Exercise 1.2: Define a function to multiply two natural numbers

```agda
mul-ℕ : ℕ → ℕ → ℕ
mul-ℕ n m = {!   !}
```

**Hint:** here again pattern match on the first variable `n`, but now you will need to use your `add-ℕ` function in the case where a recursive call to `mul-ℕ` is called for. More specifically, our cases implement the defining equations `0 * m = 0` and `(n + 1) * m = n * m + m`.

### Exercise 1.3: Define the **predecessor** function

The predecessor maps `0 ↦ 0` and maps `(n + 1) ↦ n`:

```agda 
pred-ℕ : ℕ → ℕ
pred-ℕ n = {!   !}
```

### Exercise 1.4: Define a **parity** function

First we define a new data type `Parity` which has two values `Even` and `Odd`.

```agda 
data Parity : UU lzero where
    Even : Parity
    Odd : Parity
```

Notice that now that we can define functions which take inputs of type `Parity` by pattern matching against the patterns `Even` and `Odd`. For example, here is a function to map the parity `Even` to the natural number `0` and `Odd` to the natural number `1`.

```agda 
parity-to-ℕ : Parity → ℕ
parity-to-ℕ Even = zero-ℕ
parity-to-ℕ Odd = succ-ℕ zero-ℕ
```

Now define a function which maps the even numbers in `ℕ` to the parity `Even` and the odd numbers to `Odd`.

```agda 
parity : ℕ → Parity
parity n = {!   !}
```

## Some logic

Dependent type theory invites us to regard types and mathematical propositions as interchangeable. Later we will see that homotopy type theory refines this idea a little, by identifying a suitable sub-collection of type that behave even more like traditional propositions.

Of course, if we think of types as propositions we should define some propositional connectives (and, or, implication etc).

### Conjunction (and)

We would like our conjunction operation to be given in standard **infix** notation, traditionally it **associates** to the right (so `A ∧ B ∧ C` is bracketed as `A ∧ (B ∧ C)`) and it **binds** more tightly than many other operators (so `A ∧ B ∨ C` is bracketed as `(A ∧ B) ∨ C`. The following `infix` directive instructs Agda to make `∧` into an infix operator that observes those conventions.

```agda 
infixr 2 _∧_
```

The **terms** of type `A ∧ B` should correspond to **proofs** of that proposition. Of course, to prove `A ∧ B` we must provide two proofs, one of `A` and one of `B`, so the terms of conjunction as a data type should be pairs. Accordingly we get the following data type declaration:

```agda 
data _∧_ (A B : UU lzero) : UU lzero where
    pair : A → B → A ∧ B
```

We can think of the **constructor** `pair` as an **introduction rule**, it tells us how to introduce a proof of `A ∧ B` by "combining" given proofs of `A` and `B`. We should also have some **elimination rules** which allow us to deconstruct a proof of `A ∧ B` to give the "parts" it is made up of. We have two of these for conjunction and we can define them using pattern matching.

```adga 
∧-elim-left : A ∧ B → A
∧-elim-left p = ?

∧-elim-right : A ∧ B → B
∧-elim-right p = ?
```

**Note:** `∧-elim-left` and `∧-elim-right` are the traditional names for these conjunction elimination rules. Correspondingly, the traditional name for the introduction rule `pair` is `∧-intro`, so for future use we define the following **alias**.

```agda 
∧-intro : { A B : UU lzero } → A → B → A ∧ B
∧-intro = pair
```



