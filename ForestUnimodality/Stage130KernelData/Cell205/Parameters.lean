import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell205
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 73
  A := (-8288261910373661783779653/5000000000000000000000000)
  B := (11632053082422888490299329/100000000000000000000000000)
  C := (55033596844901834857499701/10000000000000000000000000000)
  dδ := (35424554606300368009286217/500000000000000000000000000)
  dM := (2854128890326371268543193/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(64067998050047325619971161/10000000000000000000000000), (15124930172047199583573729/2500000000000000000000000), (58820239994579011977293703/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (32351/60776)
  hi := (48539/91164)
  vmin := (2068974875/8310874896)
  damping := (2068974875/8310874896)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell205
