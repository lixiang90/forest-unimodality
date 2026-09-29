import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 91
  A := (-2003841981613960961094989/1250000000000000000000000)
  B := (6022815288251779156092347/62500000000000000000000000)
  C := (3901756161044609978565123/2500000000000000000000000000)
  dδ := (60606024162297808532962051/1000000000000000000000000000)
  dM := (2512352899208513128288811/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(10536596569183615201836801/1000000000000000000000000), (2296058919024567490652089/1000000000000000000000000), (76505235604842042107520683/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (26/51)
  hi := (3579/7004)
  vmin := (12258075/49056016)
  damping := (12258075/49056016)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell082
