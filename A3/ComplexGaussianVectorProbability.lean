import A3.GaussianMatrixRank

open MeasureTheory

namespace A3Research

instance complexCircularGaussianVector_probability (d : ℕ) :
    IsProbabilityMeasure (LogdetLean.GramHafnian.circularGaussianVector d) := by
  unfold LogdetLean.GramHafnian.circularGaussianVector
  infer_instance

end A3Research
