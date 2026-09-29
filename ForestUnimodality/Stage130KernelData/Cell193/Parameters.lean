import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell193
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 88
  A := (-4189431710897107810609441/2500000000000000000000000)
  B := (5081742964290912600855421/50000000000000000000000000)
  C := (47282308336191415307214747/10000000000000000000000000000)
  dδ := (61855971031229931011985457/1000000000000000000000000000)
  dM := (10844752565653129408596023/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5770195531302476865675999/500000000000000000000000), (10214229295344365855413571/5000000000000000000000000), (36341936326880613705725409/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31933/60208)
  hi := (113/213)
  vmin := (11300/45369)
  damping := (11300/45369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell193
