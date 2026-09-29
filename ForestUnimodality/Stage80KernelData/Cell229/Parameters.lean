import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell229
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := 17
  A := (5983429212067214098169643/20000000000000000000000000)
  B := (430916446934503406807071/12500000000000000000000000)
  C := (3728879048531346107608897/40000000000000000000000000)
  dδ := (1292048753727104495880873/25000000000000000000000000)
  dM := (30000469941443352406632017/50000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(59558648358259400623637703/10000000000000000000000000)]
  retention := ![(3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (83/126)
  hi := (2/3)
  vmin := (2/9)
  damping := (80000000000000000000000000000000000000000/888264396098042275699264258736843725914681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell229
