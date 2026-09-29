import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 59
  A := (-2607012370083844434702769/2000000000000000000000000)
  B := (1454403269655731370524343/12500000000000000000000000)
  C := (-54472037067213379887831159/10000000000000000000000000000)
  dδ := (10495985550134536226640769/125000000000000000000000000)
  dM := (8324258315653145726825679/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(14339766643045762095631801/50000000000000000000000000), (680295261433190856514841/62500000000000000000000), (5805807952339965716248571/125000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9/19)
  hi := (1733/3648)
  vmin := (90/361)
  damping := (90/361)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell035
