import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell228
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (-14495568742723637988945029/50000000000000000000000000)
  B := (24613597511492977393254833/500000000000000000000000000)
  C := (2166750542495493869754597/20000000000000000000000000)
  dδ := (33733331667343546822479539/1000000000000000000000000000)
  dM := (26961710629889361432592887/50000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(16671899681436630480391159/5000000000000000000000000), (81256718694229138066909/7812500000000000000000), (16494545038711028173139539/10000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107/180)
  hi := (3/5)
  vmin := (6/25)
  damping := (6/25)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell228
