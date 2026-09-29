import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (12598695804621327043903989/50000000000000000000000000)
  B := (62878095611557799360369359/1000000000000000000000000000)
  C := (7688621689598128250420217/1000000000000000000000000000)
  dδ := (11988004815243595568841073/100000000000000000000000000)
  dM := (15532975609756009653661391/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(9404868960008719858123527/1250000000000000000000000), (4359943703068216080964703/200000000000000000000000), (1963235761256792599738219/200000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95699/180624)
  hi := (7977/15052)
  vmin := (56437275/226562704)
  damping := (56437275/226562704)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell161
