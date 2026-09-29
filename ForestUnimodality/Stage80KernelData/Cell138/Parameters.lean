import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 42
  A := (-4703008592810598931066579/20000000000000000000000000)
  B := (87844839254525089455860609/1000000000000000000000000000)
  C := (30670031626238800775974269/5000000000000000000000000000)
  dδ := (1406891254140895698709901/12500000000000000000000000)
  dM := (3641011592108052245808647/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5710294251630661399588007/1000000000000000000000000), (19875986035581900690516477/10000000000000000000000000), (16980274710582293096194917/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2326/4431)
  hi := (4657/8862)
  vmin := (19582685/78535044)
  damping := (19582685/78535044)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell138
