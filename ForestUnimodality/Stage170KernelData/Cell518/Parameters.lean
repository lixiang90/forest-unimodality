import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell518
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (100)
  A := (-10402278071877939186151707 / 5000000000000000000000000)
  B := (1378787387026659053135269 / 12500000000000000000000000)
  C := (21815315708474977522690619 / 5000000000000000000000000000)
  dδ := (29430526868516996424895993 / 500000000000000000000000000)
  dM := (10867755325483232590327853 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(7129834146025963992343577 / 1250000000000000000000000), (18432237815641659040011291 / 200000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (28 / 53)
  hi := (23881 / 45156)
  vmin := (508068275 / 2039064336)
  damping := (508068275 / 2039064336)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell518
