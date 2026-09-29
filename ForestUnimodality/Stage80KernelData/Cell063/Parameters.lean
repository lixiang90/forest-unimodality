import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 37
  A := (10806608030263882608323911/5000000000000000000000000)
  B := (-13709323060813875458374689/500000000000000000000000000)
  C := (-1321854294101522614510863/625000000000000000000000000)
  dδ := (11377725822669587651958523/100000000000000000000000000)
  dM := (42528517804792673531744107/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(32322658941961903700246239/5000000000000000000000000), (79131116099166671773446069/10000000000000000000000000), (986881036655546068914191/40000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9287/19012)
  hi := (24/49)
  vmin := (90316075/361456144)
  damping := (90316075/361456144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell063
