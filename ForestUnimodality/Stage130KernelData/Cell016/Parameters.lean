import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 35
  A := (14222665900439158571444409/100000000000000000000000000)
  B := (9464656325891314045395397/500000000000000000000000000)
  C := (-27505656192641565749301691/500000000000000000000000000)
  dδ := (19680850082757692792734261/1000000000000000000000000000)
  dM := (14060144903962673492564539/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(21935606281721349297697543/10000000000000000000000000), (2237541871712058849652749/200000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19/51)
  hi := (97/255)
  vmin := (608/2601)
  damping := (608/2601)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell016
