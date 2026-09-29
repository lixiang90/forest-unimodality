import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 73
  A := (-7497945688678171133290107/5000000000000000000000000)
  B := (10913680127881084103158571/100000000000000000000000000)
  C := (9005533060810718467420477/2500000000000000000000000000)
  dδ := (14207903072987254633474663/200000000000000000000000000)
  dM := (13445675967755546086762619/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(67513807131576255571303591/10000000000000000000000000), (25052594415077891198961879/5000000000000000000000000), (14917770990987641255287599/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22647/43472)
  hi := (109/209)
  vmin := (10900/43681)
  damping := (10900/43681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell111
