import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell171
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 39
  A := (25219921554345550818254651/10000000000000000000000000)
  B := (-988248937930037403901129/31250000000000000000000000)
  C := (2394452949278180753367451/12500000000000000000000000)
  dδ := (30346736750075344740684713/500000000000000000000000000)
  dM := 0
  wL := 0
  wR := 1
  wC := 0
  price := ![(39718448490717475074518461/10000000000000000000000000), (10157140481299280487803571/10000000000000000000000000), (16025838816595756597394029/5000000000000000000000000), (2581756446367830193366899/250000000000000000000000)]
  retention := ![(9/10), (1/2), (7/20), (3/10)]
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
end ForestUnimodality.Stage99KernelData.Cell171
