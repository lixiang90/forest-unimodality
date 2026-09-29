import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (44)
  A := (4964864970195408372610757 / 25000000000000000000000000)
  B := (549667413421804987305741 / 50000000000000000000000000)
  C := (-35554380633933145572367351 / 1000000000000000000000000000)
  dδ := (6019531120625376714727839 / 500000000000000000000000000)
  dM := (10543570914529250552756079 / 200000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(21225120145198275722897563 / 25000000000000000000000000), (16570820499147135507200801 / 2000000000000000000000000), (1550770200502309847934157 / 200000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19 / 51)
  hi := (97 / 255)
  vmin := (608 / 2601)
  damping := (608 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell064
