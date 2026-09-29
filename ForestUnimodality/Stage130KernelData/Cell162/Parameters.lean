import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 88
  A := (-16111300659356463837923457/10000000000000000000000000)
  B := (99778413700564505539603033/1000000000000000000000000000)
  C := (47327691611628776996445467/10000000000000000000000000000)
  dδ := (62972486479436956541277937/1000000000000000000000000000)
  dM := (10704287674619717991159051/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12276273445574027221027791/1000000000000000000000000), (8320730314073038202948851/10000000000000000000000000), (732222937397647513080301/10000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23881/45156)
  hi := (95549/180624)
  vmin := (8128831175/32625029376)
  damping := (8128831175/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell162
