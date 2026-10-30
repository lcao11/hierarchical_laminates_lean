module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases

/-!
# Explicit rational data for the sixteen-potential construction

All finite identities in this file are checked by kernel reduction. The spatial
index in the two loading matrices is the first index. Generator indices
begin at `0`.
-/

@[expose] public section

namespace HierarchicalLaminates

open scoped Matrix

abbrev QMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℚ

/-- Quaternion matrices with the orientation used by the generators. -/
def quaternionQ (j : Fin 4) : QMatrix 4 4 :=
  ![!![1, 0, 0, 0;
      0, 1, 0, 0;
      0, 0, 1, 0;
      0, 0, 0, 1],
    !![0, -1, 0, 0;
      1, 0, 0, 0;
      0, 0, 0, -1;
      0, 0, 1, 0],
    !![0, 0, -1, 0;
      0, 0, 0, 1;
      1, 0, 0, 0;
      0, -1, 0, 0],
    !![0, 0, 0, 1;
      0, 0, 1, 0;
      0, -1, 0, 0;
      -1, 0, 0, 0]] j

/-- The four symmetric Clifford generators. -/
def gammaQ (j : Fin 4) : QMatrix 8 8 :=
  ![!![0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 1;
      1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, -1, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, -1;
      0, 0, 0, 0, 0, 0, 1, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      -1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, -1, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, -1, 0;
      0, 0, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, -1, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, -1, 0, 0, 0, 0;
      -1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, -1, 0, 0;
      0, 0, 0, 0, -1, 0, 0, 0;
      0, 0, 0, -1, 0, 0, 0, 0;
      0, 0, -1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0, 0]] j

/-- The generator product, with opposite diagonal blocks. -/
def omegaQ : QMatrix 8 8 :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, -1, 0, 0, 0;
      0, 0, 0, 0, 0, -1, 0, 0;
      0, 0, 0, 0, 0, 0, -1, 0;
      0, 0, 0, 0, 0, 0, 0, -1]

/-- The four block rows of the rational factor. -/
def factorBlockQ (j : Fin 4) : QMatrix 4 8 :=
  ![!![(1 / 2), 0, 0, 0, (1 / 2), 0, 0, 0;
      0, (1 / 2), 0, 0, 0, (1 / 2), 0, 0;
      0, 0, (1 / 2), 0, 0, 0, (1 / 2), 0;
      0, 0, 0, (1 / 2), 0, 0, 0, (1 / 2)],
    !![(1 / 2), 0, 0, 0, 0, (-1 / 2), 0, 0;
      0, (1 / 2), 0, 0, (1 / 2), 0, 0, 0;
      0, 0, (1 / 2), 0, 0, 0, 0, (-1 / 2);
      0, 0, 0, (1 / 2), 0, 0, (1 / 2), 0],
    !![(1 / 2), 0, 0, 0, 0, 0, (-1 / 2), 0;
      0, (1 / 2), 0, 0, 0, 0, 0, (1 / 2);
      0, 0, (1 / 2), 0, (1 / 2), 0, 0, 0;
      0, 0, 0, (1 / 2), 0, (-1 / 2), 0, 0],
    !![(1 / 2), 0, 0, 0, 0, 0, 0, (1 / 2);
      0, (1 / 2), 0, 0, 0, 0, (1 / 2), 0;
      0, 0, (1 / 2), 0, 0, (-1 / 2), 0, 0;
      0, 0, 0, (1 / 2), (-1 / 2), 0, 0, 0]] j

/-- The sixteen-by-eight rational factor `P`. -/
def factorQ : QMatrix 16 8 :=
  !![(1 / 2), 0, 0, 0, (1 / 2), 0, 0, 0;
      0, (1 / 2), 0, 0, 0, (1 / 2), 0, 0;
      0, 0, (1 / 2), 0, 0, 0, (1 / 2), 0;
      0, 0, 0, (1 / 2), 0, 0, 0, (1 / 2);
      (1 / 2), 0, 0, 0, 0, (-1 / 2), 0, 0;
      0, (1 / 2), 0, 0, (1 / 2), 0, 0, 0;
      0, 0, (1 / 2), 0, 0, 0, 0, (-1 / 2);
      0, 0, 0, (1 / 2), 0, 0, (1 / 2), 0;
      (1 / 2), 0, 0, 0, 0, 0, (-1 / 2), 0;
      0, (1 / 2), 0, 0, 0, 0, 0, (1 / 2);
      0, 0, (1 / 2), 0, (1 / 2), 0, 0, 0;
      0, 0, 0, (1 / 2), 0, (-1 / 2), 0, 0;
      (1 / 2), 0, 0, 0, 0, 0, 0, (1 / 2);
      0, (1 / 2), 0, 0, 0, 0, (1 / 2), 0;
      0, 0, (1 / 2), 0, 0, (-1 / 2), 0, 0;
      0, 0, 0, (1 / 2), (-1 / 2), 0, 0, 0]

/-- The common vertical constitutive block. -/
def verticalQ : QMatrix 16 16 :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, (1 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, (1 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, (1 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, (1 / 2), 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, (1 / 3), 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, (1 / 3), 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 / 3), 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 / 3), 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 / 4), 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 / 4), 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 / 4), 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 / 4)]

def gammaSumQ : QMatrix 8 8 := ∑ j : Fin 4, gammaQ j

def gramQ : QMatrix 8 8 := 1 + (1 / 4 : ℚ) • gammaSumQ

/-- The explicit inverse of the Gram matrix. -/
def gramInvQ : QMatrix 8 8 :=
  (8 / 3 : ℚ) • (1 : QMatrix 8 8) - (4 / 3 : ℚ) • gramQ

def unitPlusQ : Fin 8 → ℚ := fun i => if i = 0 then 1 else 0

def unitMinusQ : Fin 8 → ℚ := fun i => if i = 4 then 1 else 0

def loadPlusQ : Fin 16 → ℚ := fun i => (factorQ * gramInvQ) i 0

def loadMinusQ : Fin 16 → ℚ := fun i => (factorQ * gramInvQ) i 4

def xiQ : QMatrix 2 16 := fun i j => if i = 0 then loadPlusQ j else 0

def etaQ : QMatrix 2 16 := fun i j => if i = 0 then loadMinusQ j else 0

/-- The selected reduced loading difference, with zero-based coordinates. -/
def reducedDifferenceQ (M : QMatrix 8 8) : ℚ := M 0 0 - M 4 4

set_option maxRecDepth 100000 in
theorem gammaQ_blocks :
    ∀ j r c : Fin 4,
      gammaQ j (Fin.castAdd 4 r) (Fin.castAdd 4 c) = 0 ∧
      gammaQ j (Fin.castAdd 4 r) (Fin.natAdd 4 c) = quaternionQ j r c ∧
      gammaQ j (Fin.natAdd 4 r) (Fin.castAdd 4 c) = quaternionQ j c r ∧
      gammaQ j (Fin.natAdd 4 r) (Fin.natAdd 4 c) = 0 := by
  intro j r c
  fin_cases j <;> fin_cases r <;> fin_cases c <;> decide +kernel

set_option maxRecDepth 100000 in
theorem factorBlockQ_from_quaternion :
    ∀ j r c : Fin 4,
      factorBlockQ j r (Fin.castAdd 4 c) =
        (1 / 2 : ℚ) * (if r = c then 1 else 0) ∧
      factorBlockQ j r (Fin.natAdd 4 c) = (1 / 2 : ℚ) * quaternionQ j r c := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gammaQ_transpose : ∀ j : Fin 4, (gammaQ j)ᵀ = gammaQ j := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gammaQ_clifford :
    ∀ i j : Fin 4,
      gammaQ i * gammaQ j + gammaQ j * gammaQ i =
        if i = j then (2 : ℚ) • (1 : QMatrix 8 8) else 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gammaQ_square : ∀ j : Fin 4, gammaQ j * gammaQ j = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gammaQ_orientation :
    gammaQ 0 * gammaQ 1 * gammaQ 2 * gammaQ 3 = omegaQ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem omegaQ_transpose : omegaQᵀ = omegaQ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem omegaQ_square : omegaQ * omegaQ = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem factorBlockQ_gram :
    ∀ j : Fin 4,
      (factorBlockQ j)ᵀ * factorBlockQ j =
        (1 / 4 : ℚ) • ((1 : QMatrix 8 8) + gammaQ j) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem factorQ_gram : factorQᵀ * factorQ = gramQ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gammaSumQ_square :
    gammaSumQ * gammaSumQ = (4 : ℚ) • (1 : QMatrix 8 8) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gramQ_polynomial :
    gramQ * gramQ = (2 : ℚ) • gramQ - (3 / 4 : ℚ) • (1 : QMatrix 8 8) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gramQ_mul_inv : gramQ * gramInvQ = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gramInvQ_mul : gramInvQ * gramQ = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gramQ_lower_square :
    gramQ - (1 / 2 : ℚ) • (1 : QMatrix 8 8) =
      (1 / 16 : ℚ) •
        ((gammaSumQ + (2 : ℚ) • (1 : QMatrix 8 8))ᵀ *
          (gammaSumQ + (2 : ℚ) • (1 : QMatrix 8 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gramQ_upper_square :
    (3 / 2 : ℚ) • (1 : QMatrix 8 8) - gramQ =
      (1 / 16 : ℚ) •
        ((gammaSumQ - (2 : ℚ) • (1 : QMatrix 8 8))ᵀ *
          (gammaSumQ - (2 : ℚ) • (1 : QMatrix 8 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem factorQ_loadPlus :
    factorQᵀ *ᵥ loadPlusQ = unitPlusQ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem factorQ_loadMinus :
    factorQᵀ *ᵥ loadMinusQ = unitMinusQ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem loadPlusQ_sq :
    (∑ i : Fin 16, loadPlusQ i * loadPlusQ i) = 4 / 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem loadMinusQ_sq :
    (∑ i : Fin 16, loadMinusQ i * loadMinusQ i) = 4 / 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem xiQ_sq :
    (∑ i : Fin 2, ∑ j : Fin 16, xiQ i j * xiQ i j) = 4 / 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem etaQ_sq :
    (∑ i : Fin 2, ∑ j : Fin 16, etaQ i j * etaQ i j) = 4 / 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem reducedDifferenceQ_identity :
    reducedDifferenceQ (1 : QMatrix 8 8) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem reducedDifferenceQ_gamma :
    ∀ j : Fin 4, reducedDifferenceQ (gammaQ j) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem reducedDifferenceQ_omega : reducedDifferenceQ omegaQ = 2 := by
  decide +kernel

end HierarchicalLaminates
