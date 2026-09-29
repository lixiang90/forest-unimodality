import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-811191599268531871587129/500000000000000000000000)
  B := (11205077612170594170137861/100000000000000000000000000)
  C := (24803708755936487717619343/5000000000000000000000000000)
  dδ := (70333489285692621373335953/1000000000000000000000000000)
  dM := (669598124152800868585933/500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(17173971798616542994153633/2500000000000000000000000), (6398454817300471830776587/1000000000000000000000000), (61044210517289180017996841/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (15929/30104)
  hi := (95599/180624)
  vmin := (8128304975/32625029376)
  damping := (8128304975/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell167
