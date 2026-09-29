import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 18
  A := (11920437813403962246994183/100000000000000000000000000)
  B := (9737203479735043187837107/500000000000000000000000000)
  C := (-2829624958505730369928699/100000000000000000000000000)
  dδ := (20070712837108008880226961/1000000000000000000000000000)
  dM := (7323950871903713206751557/50000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(44713383226435765571693537/100000000000000000000000000), (46379992976950843441841243/10000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19/70)
  hi := (39/140)
  vmin := (969/4900)
  damping := (387600000000000000000000000000000000000000/4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell003
