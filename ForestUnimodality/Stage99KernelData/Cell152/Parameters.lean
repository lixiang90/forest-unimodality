import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 109
  A := (8265096108335314134762939/25000000000000000000000000)
  B := (76530921693724940357839159/1000000000000000000000000000)
  C := (30063143534445213589378909/50000000000000000000000000)
  dδ := (663380448227145480544209/5000000000000000000000000)
  dM := (6687963645590752409172963/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(18823034242616714095674979/2500000000000000000000000), (4276221961270231797236363/1250000000000000000000000), (5085294020055168395799683/500000000000000000000000), (3683782173422079697644449/125000000000000000000000)]
  retention := ![(4/5), (3/5), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (24257/45582)
  hi := (32351/60776)
  vmin := (919577175/3693722176)
  damping := (919577175/3693722176)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell152
