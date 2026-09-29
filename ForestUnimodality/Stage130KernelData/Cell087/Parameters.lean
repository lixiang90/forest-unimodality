import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 75
  A := (-11345997804709030864955821/10000000000000000000000000)
  B := (45691494731829554454272113/500000000000000000000000000)
  C := (25972319481905484055139777/10000000000000000000000000000)
  dδ := (72113159565562037767172399/1000000000000000000000000000)
  dM := (5587565398297231200608337/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1056439400144145679405483/100000000000000000000000), (8317470104275297870799477/250000000000000000000000), (14980809936684567063025497/500000000000000000000000)]
  retention := ![(7/10), (1/100), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (10787/21012)
  hi := (53/103)
  vmin := (2650/10609)
  damping := (2650/10609)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell087
