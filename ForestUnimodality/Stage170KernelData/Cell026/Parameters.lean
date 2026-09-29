import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (29)
  A := (1884422191774907370920289 / 12500000000000000000000000)
  B := (764873688183257077841809 / 78125000000000000000000000)
  C := (-16772000197300827167845583 / 1000000000000000000000000000)
  dδ := (10119116960759150236626169 / 1000000000000000000000000000)
  dM := (39679610353286443806108269 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(104276248936362463837213 / 2000000000000000000000)]
  retention := ![(1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (37 / 126)
  hi := (19 / 63)
  vmin := (3293 / 15876)
  damping := (32930000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell026
