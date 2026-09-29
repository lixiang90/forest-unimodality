import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 20
  A := (1454606362854468193468449/10000000000000000000000000)
  B := (3552538249769834205471497/250000000000000000000000000)
  C := (-11015264967850161431650591/500000000000000000000000000)
  dδ := (1534202565800644839366651/100000000000000000000000000)
  dM := (41824423536380417299428147/500000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(2270663054458470941909809/2000000000000000000000000), (908839024978215093142353/200000000000000000000000)]
  retention := ![(3/5), (1/1000)]
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
end ForestUnimodality.Stage130KernelData.Cell003
