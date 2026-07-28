## Preamble

### File options

First we specify the command line options that should be supplied to the Agda compiler / interpreter when this script is processed. These are supplied in a specially formatted comment block.

In the following code we've set the following options:
* `--without-K` disables Streicher’s K axiom, which we don’t want for univalent mathematics. We'll explain why later.
* `--exact-split` makes Agda to only accept definitions with the equality sign “=” that behave like so-called judgmental or definitional equalities.
* `--safe` disables features that may make Agda inconsistent, such as `--type-in-type`, postulates and more.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}
```

### Module declaration and imports

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
* `public` modifer specifies that the definitions imported by this stanza should be re-exported to any modules that import this one.

## Code

### Standard definitions

This following code sets up the notation for the **universes** `UU i` which are _types of types_ Formally, `UU` is a function which takes as input a **level** `i : Level` and produces `UU i`, the type of types of level at most i. 

To avoid Russell's paradox, the type `UU i` is a type of the next universe level `UU (lsuc i).

**The takeway:** to declare that "`A` is a type of arbitrary universe level" write `A : UU i` in a context where `i : Level`.

```agda 
UU : (i : Level) → Set (lsuc i)
UU i = Set i
```

### Natural numbers

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

**Note:** To insert the natural number symbol ℕ type the character sequence "\\-b-N". Watch what happens at the bottom of the Visual Studio Code as you do for clues on how to insert other mathematical characters. By typing "\\" we enter _unicode input mode_, which allows us to translate the subsequent character sequence into a unicode symbol.

We'll just amuse ourselves with some basic exercises:

#### Exercise 1.1: Define a function to add two natual numbers:

```agda 
add-ℕ : ℕ → ℕ → ℕ
add-ℕ n m = {!   !}
```

**Hint:** pattern match the first parameter `n`, you'll then get two cases `n = ℕ-zero` and `n = ℕ-zero n'`for some value `n'`. The first case is easy (0 + m = m) but the second case requires us to **recurse** by computing `add-ℕ n' m` and then returning its successor.

#### Exercise 1.2: Define a function to multiply two natural numbers

```agda
mul-ℕ : ℕ → ℕ → ℕ
mul-ℕ n m = {!   !}
```

**Hint:** here again pattern match on the first variable `n`, but now you will need to use your `add-ℕ` function in the case where a recursive call back to `mul-ℕ` is called for. More specifically, our cases implement the defining equations `0 * m = 0` and `(n + 1) * m = n * m + m`.
