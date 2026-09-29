import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 61
  A := (-13126102303906607176919863/25000000000000000000000000)
  B := (2301551874034332527407809/31250000000000000000000000)
  C := (29564808984125874255499689/10000000000000000000000000000)
  dδ := (19620905032522905492298193/250000000000000000000000000)
  dM := (334102954326792090950643/312500000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(685936640486570436969771/500000000000000000000000), (74859352931337097558639471/10000000000000000000000000), (7281764315020270217360121/1000000000000000000000000), (44259865879484912909447303/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27/52)
  hi := (22597/43472)
  vmin := (471712375/1889814784)
  damping := (471712375/1889814784)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell101
