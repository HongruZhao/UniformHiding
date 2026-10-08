import A1.Target

open scoped MatrixOrder ComplexOrder
open Matrix

noncomputable section
namespace A1Research

/-- Normalized symmetric overlap of a Hermitian Gram and a transpose Gram. -/
def normalizedComplexPairOverlap {m : ℕ} (T Z : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  (CFC.sqrt T).transpose⁻¹ * Z * (CFC.sqrt T)⁻¹

/-- The literal Gaussian normalized transpose Gram, with totalized inverses. -/
def normalizedTransposeGram {n m : ℕ} (G : Matrix (Fin n) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  normalizedComplexPairOverlap (G.conjTranspose * G) (G.transpose * G)

end A1Research
