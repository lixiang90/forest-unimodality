import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell188
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (137)
  A := (-9926422501204878684433197 / 5000000000000000000000000)
  B := (84397794954505653275411703 / 1000000000000000000000000000)
  C := (1798556420335896009667781 / 625000000000000000000000000)
  dδ := (45824815448207371904043583 / 1000000000000000000000000000)
  dM := (16596234398844002169010059 / 25000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(30445049747178359211829957 / 1000000000000000000000000), (10452672862740499226674729 / 100000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11 / 21)
  hi := (111 / 211)
  vmin := (11100 / 44521)
  damping := (11100 / 44521)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell188
