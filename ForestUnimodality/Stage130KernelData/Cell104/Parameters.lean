import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 90
  A := (-3207034327559225108643659/2000000000000000000000000)
  B := (98175721488236514233882701/1000000000000000000000000000)
  C := (764628789294809901866401/250000000000000000000000000)
  dδ := (12403663979723124344278773/200000000000000000000000000)
  dM := (2079241233020165564859827/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(6066317640011605227812197/500000000000000000000000), (241660791597182766921037/100000000000000000000000), (73788289835483922729508777/1000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22331/43056)
  hi := (27/52)
  vmin := (675/2704)
  damping := (675/2704)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell104
