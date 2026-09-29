import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 36
  A := (766168474536035075232121/400000000000000000000000)
  B := (-16057409009654476789163979/1000000000000000000000000000)
  C := (-32277004858258769373624553/10000000000000000000000000000)
  dδ := (5443822142460345153702761/50000000000000000000000000)
  dM := (56703386218795372598205917/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(60433780255087441446448793/10000000000000000000000000), (54829649547771106554705511/10000000000000000000000000), (13141719731845425300775787/500000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9237/19012)
  hi := (4631/9506)
  vmin := (90291675/361456144)
  damping := (90291675/361456144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell053
