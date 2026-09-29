import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell533
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (72)
  A := (-10023352930246582259599109 / 10000000000000000000000000)
  B := (72740016631933357427186593 / 1000000000000000000000000000)
  C := (3696541826329951541119101 / 20000000000000000000000000)
  dδ := (7998229573086559907046933 / 200000000000000000000000000)
  dM := (70002390992012148481643541 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(27588848998447215166152091 / 5000000000000000000000000), (12627543334051983592303259 / 500000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5 / 9)
  hi := (116 / 207)
  vmin := (10556 / 42849)
  damping := (10556 / 42849)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell533
