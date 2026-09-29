import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell213
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 91
  A := (-2975593933241889790224377/2000000000000000000000000)
  B := (2275471034787598378912321/20000000000000000000000000)
  C := (6532688797004128078427243/20000000000000000000000000)
  dδ := (4215449749939142488897037/62500000000000000000000000)
  dM := (6508319918091383339195377/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(76351298399966323060539253/10000000000000000000000000), (10416300093885626054657223/1000000000000000000000000), (21813334460280529469855537/1000000000000000000000000)]
  retention := ![(7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (643/1188)
  hi := (6/11)
  vmin := (30/121)
  damping := (30/121)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell213
