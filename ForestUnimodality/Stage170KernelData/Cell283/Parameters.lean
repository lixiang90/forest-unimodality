import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell283
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (57)
  A := (-88543797827378690747934797 / 1000000000000000000000000000)
  B := (585857369431052221915579 / 31250000000000000000000000)
  C := (55569884404347257012002359 / 1000000000000000000000000000)
  dδ := (14349537860131681907271961 / 1000000000000000000000000000)
  dM := (5035632578879117800295731 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(3345373878606706874450083 / 500000000000000000000000), (4146033089007015171034709 / 250000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 90)
  hi := (107 / 180)
  vmin := (7811 / 32400)
  damping := (7811 / 32400)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell283
