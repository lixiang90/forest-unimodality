import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 61
  A := (-45680125374962873340933811/50000000000000000000000000)
  B := (45998661813791121011352203/500000000000000000000000000)
  C := (30669346226084065638872733/10000000000000000000000000000)
  dδ := (7921592755608679314871523/100000000000000000000000000)
  dM := (12919191587002685182861139/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(42472956647413786512856859/5000000000000000000000000), (2496605785352221573702991/50000000000000000000000), (3167102926122540740294653/2000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7339/14214)
  hi := (107/207)
  vmin := (10700/42849)
  damping := (10700/42849)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell091
