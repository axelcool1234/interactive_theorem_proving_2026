/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe01_TypesAndTerms_Demo


/- # LoVe Exercise 1: Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Terms

Complete the following definitions, by replacing the `sorry` markers by terms
of the expected type.

Hint: A procedure for doing so systematically is described in Section 1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def I : α → α :=
  fun a ↦ a

def K : α → β → α :=
  fun a b ↦ a

def C : (α → β → γ) → β → α → γ :=
  fun f b a ↦ f a b

def projFst : α → α → α :=
  fun x y ↦ x

/- Give a different answer than for `projFst`. -/

def projSnd : α → α → α :=
  fun x y ↦ y

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  fun f a g b ↦ g a


/- ## Question 2: Typing Derivation

Show the typing derivation for your definition of `C` above, on paper or using
ASCII or Unicode art. Start with an empty context. You might find the
characters `–` (to draw horizontal bars) and `⊢` useful. -/

-- write your solution in a comment here or on paper

/-
----------------- Var     ----------- Var
C ⊢ f : α → β → γ          C ⊢ a : α
-------------------------------------- App       ---------- Var
C ⊢ f a : β → γ                                   C ⊢ b : β
------------------------------------------------------------- App
f : α → β → γ, b : β, a : α ⊢ f a b : γ
------------------------------------------ Fun
f : α → β → γ, b : β ⊢ (fun (a : α) ↦ f a b) : α → γ
------------------------------------------------------- Fun
f : α → β → γ ⊢ (fun (b : β) (a : α) ↦ f a b) : β → α → γ
----------------------------------------------------------------- Fun
⊢ (fun (f : α → β → γ) (b : β) (a : α) ↦ f a b) : (α → β → γ) → β → α → γ 

-/

end LoVe
