import A4.FullTheorem
import LogdetLean.GaussianScatter

/-!
This copied provider replaces the historical A4 axiom with the exact proved
Matsumoto theorem. Original research and hiding sources are preserved.
-/

/- Keep the old consumer's rectangular Gaussian measurable structure.
The standalone provider has already checked its internal Borel instance. -/
attribute [-instance] A4Research.InverseStein.instMeasurableSpaceMatrixFinReal_a4
attribute [instance 2000] LogdetLean.realMatrixMeasurableSpace
attribute [instance 3000] MatsumotoPaper.instMeasurableSpaceRealMatrix

noncomputable section
namespace MatsumotoPaper

theorem A4_matsumoto_theorem_3 : Target := completedMatsumotoTheorem3

end MatsumotoPaper

#print axioms MatsumotoPaper.A4_matsumoto_theorem_3
