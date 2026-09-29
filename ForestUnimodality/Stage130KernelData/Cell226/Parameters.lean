import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell226
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 44
  A := (-37295159651412983613738561/100000000000000000000000000)
  B := (2751256698270150569118897/50000000000000000000000000)
  C := (6606930742419840629775507/50000000000000000000000000)
  dδ := (1901357127428808177493913/50000000000000000000000000)
  dM := (61467803797535670428525689/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(19567564628398002035680747/5000000000000000000000000), (66704231288841953073642799/10000000000000000000000000), (72062899248584306732823279/10000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7/12)
  hi := (53/90)
  vmin := (1961/8100)
  damping := (1961/8100)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell226
