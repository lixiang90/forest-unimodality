import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (58)
  A := (-33928095126498825635508183 / 500000000000000000000000000)
  B := (23516112019167537822150749 / 1000000000000000000000000000)
  C := (-1021208580414832527150093 / 12500000000000000000000000)
  dδ := (10328350337044552020859811 / 500000000000000000000000000)
  dM := (3812356057410869875339693 / 25000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(1005005034703573052468073 / 125000000000000000000000), (3210239610701574264339797 / 200000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7 / 17)
  hi := (64 / 153)
  vmin := (70 / 289)
  damping := (70 / 289)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell084
