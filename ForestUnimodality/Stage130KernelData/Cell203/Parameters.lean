import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell203
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 73
  A := (-16739151949226873006182359/10000000000000000000000000)
  B := (5850822364825893073803087/50000000000000000000000000)
  C := (54916598694495864091402737/10000000000000000000000000000)
  dδ := (35405481047586104259572437/500000000000000000000000000)
  dM := (3586504324909541995165807/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(30803414762514109703772647/5000000000000000000000000), (31875533039989849548589973/5000000000000000000000000), (14681246485587701400277183/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
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
end ForestUnimodality.Stage130KernelData.Cell203
