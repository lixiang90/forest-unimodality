import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell332
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (32)
  A := (7437863476355372927883991 / 100000000000000000000000000)
  B := (5239063024861731129866449 / 500000000000000000000000000)
  C := (3830617029671876117014051 / 200000000000000000000000000)
  dδ := (89865991067340691283993337 / 10000000000000000000000000000)
  dM := (47516802423897324325011843 / 1000000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(17860691362768301715391317 / 10000000000000000000000000), (91808147348665514186905057 / 10000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (83 / 126)
  hi := (2 / 3)
  vmin := (2 / 9)
  damping := (80000000000000000000000000000000000000000 / 888264396098042275699264258736843725914681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell332
