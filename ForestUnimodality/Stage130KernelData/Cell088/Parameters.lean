import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 90
  A := (-7948088994065524942556067/5000000000000000000000000)
  B := (19292869828672717935624803/200000000000000000000000000)
  C := (9788279195470821810592943/5000000000000000000000000000)
  dδ := (7526698623180275680988327/125000000000000000000000000)
  dM := (10159529725416538512711151/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2976535476075599540024541/250000000000000000000000), (752497018421821639577729/12500000000000000000000), (812311644499621010595547/50000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
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
end ForestUnimodality.Stage130KernelData.Cell088
