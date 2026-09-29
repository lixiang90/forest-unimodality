import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (114)
  A := (-44307755500460082153324493 / 100000000000000000000000000)
  B := (24230155809137607358927369 / 1000000000000000000000000000)
  C := (-5522129207101712788929859 / 50000000000000000000000000)
  dδ := (3644389294854580296778579 / 200000000000000000000000000)
  dM := (5782816594244868864697559 / 50000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(6370733452741043301159607 / 500000000000000000000000), (38209323531419521202678879 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell108
