import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell454
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (84)
  A := (-18319806321127408499194189 / 20000000000000000000000000)
  B := (2088352831327037507913591 / 31250000000000000000000000)
  C := (-10990273940959380261084277 / 50000000000000000000000000)
  dδ := (1801005174614920545383967 / 40000000000000000000000000)
  dM := (60888149392107453194977751 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(19980770051105427143056659 / 1000000000000000000000000), (8401191494308800855606023 / 500000000000000000000000)]
  retention := ![(3 / 5), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4 / 9)
  hi := (301 / 666)
  vmin := (20 / 81)
  damping := (20 / 81)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell454
