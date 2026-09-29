import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell482
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (104)
  A := (-3654647534352618667412571 / 2000000000000000000000000)
  B := (2435957079942475608791419 / 25000000000000000000000000)
  C := (4126839127164649671797303 / 200000000000000000000000000000)
  dδ := (57026853860719851907479239 / 1000000000000000000000000000)
  dM := (46651639188019207796220833 / 50000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(19867190805387766605605293 / 2500000000000000000000000), (47084401845501744787725329 / 500000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1 / 2)
  hi := (405 / 808)
  vmin := (163215 / 652864)
  damping := (163215 / 652864)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell482
