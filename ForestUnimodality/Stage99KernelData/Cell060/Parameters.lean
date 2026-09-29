import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 51
  A := (-11299992640148129674315669/20000000000000000000000000)
  B := (87742550993751194932102067/1000000000000000000000000000)
  C := (43297986486627685091474471/500000000000000000000000000000)
  dδ := (911237381465789947343481/10000000000000000000000000)
  dM := (3640021698474955945228071/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(67310866386110355108485237/10000000000000000000000000), (34674225020451473255889141/1000000000000000000000000), (17877323133524317455567143/2000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1/2)
  hi := (405/808)
  vmin := (163215/652864)
  damping := (163215/652864)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell060
