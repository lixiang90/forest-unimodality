import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell184
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 18
  A := (1455490406061335742549101/6250000000000000000000000)
  B := (12651953864697366297642489/500000000000000000000000000)
  C := (7325011278694877267514407/125000000000000000000000000)
  dδ := (32904746896018896573643531/1000000000000000000000000000)
  dM := (31605496050142564863627559/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(21312812344840401657108941/10000000000000000000000000), (20050511966802542218601957/5000000000000000000000000)]
  retention := ![(7/10), (3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2/3)
  hi := (35/52)
  vmin := (595/2704)
  damping := (1487500000000000000000000000000000000000000/16679631437841016065908406636280732186620121)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell184
