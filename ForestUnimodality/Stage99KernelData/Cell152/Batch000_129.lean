import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell152.Parameters
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch000_049
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch050_099
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch100_149
import ForestUnimodality.BinomialMassData.Q32351_60776.Batch000_049
import ForestUnimodality.BinomialMassData.Q32351_60776.Batch050_099
import ForestUnimodality.BinomialMassData.Q32351_60776.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree000.table
  base := (1256510821230410822085588061/25000000000000000000000000)
  polynomial :=
    { denominator := 455820000000000000000000000000000000000000000
      center := (2644013)
      previous := (0)
      next := (2324425)
      square := (60476415182179490588332269276000000000000000)
      linear := (-274067641717416345166213886007600000000000000)
      constant := (22909710501329834436922109998600800000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree000.table
  base := (1256510821230410822085588061/25000000000000000000000000)
  polynomial :=
    { denominator := 607760000000000000000000000000000000000000000
      center := (3526259)
      previous := (0)
      next := (3098325)
      square := (80635220242905987451109692368000000000000000)
      linear := (-365423522289888460221618514676800000000000000)
      constant := (30546280668439779249229479998134400000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree001.table
  base := (299404910165320953496439433884991195580499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-2571084008485254608628118843942381200000000000000)
      constant := (104917985920528571745021488961510184138791470260546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree001.table
  base := (11974109921528279072056764033892254553947/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-3428280001355845532311348270448941600000000000000)
      constant := (139867033902235266783419248618265385101721944464600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (4989556882891020407/10000000000000000000)
  directionHi := (49895568828910204071/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree002.table
  base := (187046692726886944024961990005171162562597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-3060076142843297243028510795885025200000000000000)
      constant := (67508201438538914157763928028881935946859268161038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree002.table
  base := (37397834514121725826940705977071892962883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-4080437503875408432319060684898233600000000000000)
      constant := (89985496253401721401336723736525172314562051245880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4989556882891020407/10000000000000000000)
  centralHi := (49895568828910204071/100000000000000000000)
  directionLo := (70562990140165057963/100000000000000000000)
  directionHi := (17640747535041264491/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree003.table
  base := (15414799285157617664290014226427791389271/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-3549068277201339877428902747827669200000000000000)
      constant := (47198522106211586613306343381129763337939105880272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree003.table
  base := (30817420898349149429274376276267219659277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-4732595006394971332326773099347525600000000000000)
      constant := (62910818972922506211641114554879469928667309513376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70562990140165057963/100000000000000000000)
  centralHi := (17640747535041264491/25000000000000000000)
  directionLo := (21605415071055605011/25000000000000000000)
  directionHi := (17284332056844484009/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree004.table
  base := (21463385506744190743021789822694920612277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-4038060411559382511829294699770313200000000000000)
      constant := (36243741368639418810058075315310771930547644783032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree004.table
  base := (1716312646226510517870377972656534816543/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-5384752508914534232334485513796817600000000000000)
      constant := (48310438145308439059594166219826641169881067234800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21605415071055605011/25000000000000000000)
  centralHi := (17284332056844484009/20000000000000000000)
  directionLo := (4989556882891020407/5000000000000000000)
  directionHi := (99791137657820408141/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree005.table
  base := (7845185987768148754125892808911631995307/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-4527052545917425146229686651712957200000000000000)
      constant := (30526288872708820571711079939497505144062445371024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree005.table
  base := (62732579058708192402718061648722089306699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-6036910011434097132342197928246109600000000000000)
      constant := (40692509325029155513633814066577017166650820207128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4989556882891020407/5000000000000000000)
  centralHi := (99791137657820408141/100000000000000000000)
  directionLo := (111569883677462790327/100000000000000000000)
  directionHi := (13946235459682848791/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree006.table
  base := (953800885435904555043720901413545972311/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-5016044680275467780630078603655601200000000000000)
      constant := (27846488087163039735203373056906266315877918759700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree006.table
  base := (47667708262461696014694539545376425349283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-6689067513953660032349910342695401600000000000000)
      constant := (37123840541792847953801263635961181172531895349976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111569883677462790327/100000000000000000000)
  centralHi := (13946235459682848791/12500000000000000000)
  directionLo := (122218684056747614613/100000000000000000000)
  directionHi := (61109342028373807307/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree007.table
  base := (37221289380388683491413730252524087189959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-5505036814633510415030470555598245200000000000000)
      constant := (27020759007227300710280261475602439102597726515386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree007.table
  base := (37203480970285908346504696401281110422703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-7341225016473222932357622757144693600000000000000)
      constant := (36026501868667667578130773907810801497280350620216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122218684056747614613/100000000000000000000)
  centralHi := (61109342028373807307/50000000000000000000)
  directionLo := (66005633322701345687/50000000000000000000)
  directionHi := (1056090133163221531/800000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree008.table
  base := (29496506156177644695254570961847536416531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-5994028948991553049430862507540889200000000000000)
      constant := (27405453089136755276217863477448498274316386971074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree008.table
  base := (14740876173496583725353558200135102634531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-7993382518992785832365335171593985600000000000000)
      constant := (36542559457659547879515381874499719499300794514864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66005633322701345687/50000000000000000000)
  centralHi := (1056090133163221531/800000000000000000)
  directionLo := (141125980280330115927/100000000000000000000)
  directionHi := (17640747535041264491/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree009.table
  base := (23489068837006430426679067746067854179737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-6483021083349595683831254459483533200000000000000)
      constant := (28645063738129465285376836403615646467290204382598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree009.table
  base := (5869097377555518069674947993440533787277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-8645540021512348732373047586043277600000000000000)
      constant := (38198232085880850570498726391754234743671160777376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141125980280330115927/100000000000000000000)
  centralHi := (17640747535041264491/12500000000000000000)
  directionLo := (14968670648673061221/10000000000000000000)
  directionHi := (149686706486730612211/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree010.table
  base := (3723839143422380732102187723201302333773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-6972013217707638318231646411426177200000000000000)
      constant := (30538820403222642653392776839167184566720883054710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree010.table
  base := (9303984249202549471918897160942291999157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-9297697524031911632380760000492569600000000000000)
      constant := (40725990861313108813392046991320667253388396051408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14968670648673061221/10000000000000000000)
  centralHi := (149686706486730612211/100000000000000000000)
  directionLo := (78891821324528241513/50000000000000000000)
  directionHi := (157783642649056483027/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree011.table
  base := (7274634611062254726399078261863932317091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-7461005352065680952632038363368821200000000000000)
      constant := (32969810691779772913166368591561390305162891970628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree011.table
  base := (14539109869483509405621232045265440682971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-9949855026551474532388472414941861600000000000000)
      constant := (43970062543098964133849189299767462107137821033112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78891821324528241513/50000000000000000000)
  centralHi := (157783642649056483027/100000000000000000000)
  directionLo := (10342805031677983071/6250000000000000000)
  directionHi := (165484880506847729137/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree012.table
  base := (11074662580820057677336328523212292921011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-7949997486423723587032430315311465200000000000000)
      constant := (35867175124800162026872479948298516004826201284994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree012.table
  base := (2213067402563532354636030029295961420129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-10602012529071037432396184829391153600000000000000)
      constant := (47836037157339296182244537728830823177981837550440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10342805031677983071/6250000000000000000)
  centralHi := (165484880506847729137/100000000000000000000)
  directionLo := (172843320568444840089/100000000000000000000)
  directionHi := (17284332056844484009/10000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree013.table
  base := (403258913614002243931641375027629109919/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-8438989620781766221432822267254109200000000000000)
      constant := (39185828064445350609921822242959378330020534744520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree013.table
  base := (402827174416320991374113126531414149029/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-11254170031590600332403897243840445600000000000000)
      constant := (52263842573663091447138548727422456057271465417760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172843320568444840089/100000000000000000000)
  centralHi := (17284332056844484009/10000000000000000000)
  directionLo := (22487628978884806607/12500000000000000000)
  directionHi := (179901031831078452857/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree014.table
  base := (5433377594029000199224891431313926242571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-8927981755139808855833214219196753200000000000000)
      constant := (42895490672492746837103276177056586879357455433234) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree014.table
  base := (1085068830982204730396083258818889632099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-11906327534110163232411609658289737600000000000000)
      constant := (57213131737879177614799956291823515526112848579640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22487628978884806607/12500000000000000000)
  centralHi := (179901031831078452857/100000000000000000000)
  directionLo := (23336515459497435133/12500000000000000000)
  directionHi := (37338424735195896213/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree015.table
  base := (155862546516139823516868115802051437499/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-9416973889497851490233606171139397200000000000000)
      constant := (46974689858992414339816632763669033164342626770920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree015.table
  base := (1554880030779469109426225276594521120767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-12558485036629726132419322072739029600000000000000)
      constant := (62655288021762527399448323841993654355969360507248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23336515459497435133/12500000000000000000)
  centralHi := (37338424735195896213/20000000000000000000)
  directionLo := (48311176780978781791/25000000000000000000)
  directionHi := (38648941424783025433/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree016.table
  base := (1070576082006926598535665199963359774031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-9905966023855894124633998123082041200000000000000)
      constant := (51407419502503057058558586360712019986075436276074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree016.table
  base := (1063586143092873715586234122560042564959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-13210642539149289032427034487188321600000000000000)
      constant := (68568977841077030707076783724388380989211622353848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48311176780978781791/25000000000000000000)
  centralHi := (38648941424783025433/20000000000000000000)
  directionLo := (199582275315640816281/100000000000000000000)
  directionHi := (99791137657820408141/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree017.table
  base := (-371285343973660549464841787782275085817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-10394958158213936759034390075024685200000000000000)
      constant := (56181239699514573928521445301702261272959770754164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree017.table
  base := (-93636496062082637009134367085104104707/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-13862800041668851932434746901637613600000000000000)
      constant := (74937618983628477192032884787876884939175128117568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199582275315640816281/100000000000000000000)
  centralHi := (99791137657820408141/50000000000000000000)
  directionLo := (102862350265936424749/50000000000000000000)
  directionHi := (205724700531872849499/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree018.table
  base := (-2351036319438578651452293481787434590869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-10883950292571979393434782026967329200000000000000)
      constant := (61286161145500716544795672792581603293771033211474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree018.table
  base := (-1178558083600584683230106506711503080273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-14514957544188414832442459316086905600000000000000)
      constant := (81747894706487584811570967329614788859525827941488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102862350265936424749/50000000000000000000)
  centralHi := (205724700531872849499/100000000000000000000)
  directionLo := (21168897042049517389/10000000000000000000)
  directionHi := (211688970420495173891/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree019.table
  base := (-1889277946405554174563976807725112822193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-11372942426930022027835173978909973200000000000000)
      constant := (66713964703653665219698078706706380548105707052756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree019.table
  base := (-946054702567323571224065133357216438407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-15167115046707977732450171730536197600000000000000)
      constant := (88988847417872095103902701205487335805912162993184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21168897042049517389/10000000000000000000)
  centralHi := (211688970420495173891/100000000000000000000)
  directionLo := (217489742255697650803/100000000000000000000)
  directionHi := (54372435563924412701/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree020.table
  base := (-5045006352447741593077497870227465841007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-11861934561288064662235565930852617200000000000000)
      constant := (72457767257386734048854677849513022680511558180822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree020.table
  base := (-5050275309304777708827531508193119449621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-15819272549227540632457884144985489600000000000000)
      constant := (96651300336707274441099476316279835624789749688088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217489742255697650803/100000000000000000000)
  centralHi := (54372435563924412701/25000000000000000000)
  directionLo := (111569883677462790327/50000000000000000000)
  directionHi := (44627953470985116131/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree021.table
  base := (-3083623235376467990331307518929211410447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-12350926695646107296635957882795261200000000000000)
      constant := (78511730842185190357081731253858594207319939630124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree021.table
  base := (-6172143471361453985697647560777974509923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-16471430051747103532465596559434781600000000000000)
      constant := (104727469956023938178788418399635039817541835355944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111569883677462790327/50000000000000000000)
  centralHi := (44627953470985116131/20000000000000000000)
  directionLo := (228650221001360126519/100000000000000000000)
  directionHi := (5716255525034003163/2500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree022.table
  base := (-7159707547963379184894801917092765143097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-12839918830004149931036349834737905200000000000000)
      constant := (84870858094263462209386576192071720769542137291962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree022.table
  base := (-716425386839392257634395114393682893223/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-17123587554266666432473308973884073600000000000000)
      constant := (113210693460366952855257960537222766078737955983440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228650221001360126519/100000000000000000000)
  centralHi := (5716255525034003163/2500000000000000000)
  directionLo := (117015481190237540991/50000000000000000000)
  directionHi := (234030962380475081983/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree023.table
  base := (-321393103529338626500319104831572415747/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-13328910964362192565436741786680549200000000000000)
      constant := (91530841901268087080829567393037696622668940221550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree023.table
  base := (-1004880480881258347552243463464165415413/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-17775745056786229332481021388333365600000000000000)
      constant := (122095228336845832744585250384966632473756749701312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117015481190237540991/50000000000000000000)
  centralHi := (234030962380475081983/100000000000000000000)
  directionLo := (59822685465826767457/25000000000000000000)
  directionHi := (239290741863307069829/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree024.table
  base := (-8803382592977785775877428396345215754759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-13817903098720235199837133738623193200000000000000)
      constant := (98487950679880907490961191964910393476419572265414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree024.table
  base := (-2201822186333166727585805723295068828611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-18427902559305792232488733802782657600000000000000)
      constant := (131376099447343732198063387119383408638156603011232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59822685465826767457/25000000000000000000)
  centralHi := (239290741863307069829/100000000000000000000)
  directionLo := (122218684056747614613/50000000000000000000)
  directionHi := (244437368113495229227/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree025.table
  base := (-4737373509647527690130597424483729094787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-14306895233078277834237525690565837200000000000000)
      constant := (105738938182595033998310565771524673342139159769404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree025.table
  base := (-9478362321652411686495475308391789657893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-19080060061825355132496446217231949600000000000000)
      constant := (141048978784446397785456773115465372205539146558104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122218684056747614613/50000000000000000000)
  centralHi := (244437368113495229227/100000000000000000000)
  directionLo := (249477844144551020351/100000000000000000000)
  directionHi := (3898091314758609693/1562500000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree026.table
  base := (-10057103305888604860275572137859328879781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-14795887367436320468637917642508481200000000000000)
      constant := (113280970941726817965998455811582663051400845213426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree026.table
  base := (-2012089255030689736311317174241016698369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-19732217564344918032504158631681241600000000000000)
      constant := (151110088732708067243036453955752468507780076043160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249477844144551020351/100000000000000000000)
  centralHi := (3898091314758609693/1562500000000000000)
  directionLo := (127209239550212512683/50000000000000000000)
  directionHi := (254418479100425025367/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree027.table
  base := (-2639403342527098324530564354158207133167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-15284879501794363103038309594451125200000000000000)
      constant := (121111568882313300986404141864978169587432375120728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree027.table
  base := (-10560701748161473287156907371976688165157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-20384375066864480932511871046130533600000000000000)
      constant := (161556122883352001410466674778189272696165354822296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127209239550212512683/50000000000000000000)
  centralHi := (254418479100425025367/100000000000000000000)
  directionLo := (129632490426333630067/50000000000000000000)
  directionHi := (51852996170533452027/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree028.table
  base := (-10982560821144599189209197901417303808593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-15773871636152405737438701546393769200000000000000)
      constant := (129228556075609694336725750606818589889881635300778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree028.table
  base := (-10985411549066799393511773455007224677519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-21036532569384043832519583460579825600000000000000)
      constant := (172384180367793342627761284670626772296054202629832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129632490426333630067/50000000000000000000)
  centralHi := (51852996170533452027/20000000000000000000)
  directionLo := (66005633322701345687/25000000000000000000)
  directionHi := (264022533290805382749/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree029.table
  base := (-11337470071083473911350246356415375197809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-16262863770510448371839093498336413200000000000000)
      constant := (137630019492544215285187508691310100371671172820714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree029.table
  base := (-11340099273979226761205614575229515728661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-21688690071903606732527295875029117600000000000000)
      constant := (183591710857351836556596508446600575332913008189208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66005633322701345687/25000000000000000000)
  centralHi := (264022533290805382749/100000000000000000000)
  directionLo := (268695861289404590271/100000000000000000000)
  directionHi := (4198372832646946723/1562500000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree030.table
  base := (-11627206879350513905234149820717544603471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-16751855904868491006239485450279057200000000000000)
      constant := (146314274186539391592153688588583051743677191318166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree030.table
  base := (-465185194444346927141681018753269753453/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-22340847574423169632535008289478409600000000000000)
      constant := (195176468135758627812248113443913786872376879144600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268695861289404590271/100000000000000000000)
  centralHi := (4198372832646946723/1562500000000000000)
  directionLo := (273289285671457430807/100000000000000000000)
  directionHi := (34161160708932178851/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree031.table
  base := (-11856063762902349730888661720265339726253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-17240848039226533640639877402221701200000000000000)
      constant := (155279833717119576789204245423181800767090517923138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree031.table
  base := (-11858295009604290552173926242625265347127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-22993005076942732532542720703927701600000000000000)
      constant := (207136470659973723553566528045855732466179082776456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273289285671457430807/100000000000000000000)
  centralHi := (34161160708932178851/12500000000000000000)
  directionLo := (55561353997747745093/20000000000000000000)
  directionHi := (138903384994369362733/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree032.table
  base := (-2405566586884370815147934475016966378621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-17729840173584576275040269354164345200000000000000)
      constant := (164525384892402005066877017248391594014550562500330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree032.table
  base := (-46991742675582091202726354181936963411/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-23645162579462295432550433118376993600000000000000)
      constant := (219469967880183307478887742639656502387670038325248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55561353997747745093/20000000000000000000)
  centralHi := (138903384994369362733/50000000000000000000)
  directionLo := (141125980280330115927/50000000000000000000)
  directionHi := (56450392112132046371/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree033.table
  base := (-12145868873182331324324011544654795364187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-18218832307942618909440661306106989200000000000000)
      constant := (174049766101654107352988092854400853859240045177102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree033.table
  base := (-1518469611954604733637360958954799159581/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-24297320081981858332558145532826285600000000000000)
      constant := (232175411347192173584919081348355004612629497431744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141125980280330115927/50000000000000000000)
  centralHi := (56450392112132046371/20000000000000000000)
  directionLo := (286628220922324769219/100000000000000000000)
  directionHi := (14331411046116238461/5000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree034.table
  base := (-6106571108484052480581433067221560205907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-18707824442300661543841053258049633200000000000000)
      constant := (183851948653251431851293706539843871367897910232444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree034.table
  base := (-12214877189669761758549210487386849244599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-24949477584501421232565857947275577600000000000000)
      constant := (245251429827587972663192866395688445731806978184072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286628220922324769219/100000000000000000000)
  centralHi := (14331411046116238461/5000000000000000000)
  directionLo := (58187732321463612841/20000000000000000000)
  directionHi := (145469330803659032103/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree035.table
  base := (-12232286344937359843361909007200393290991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-19196816576658704178241445209992277200000000000000)
      constant := (193931020643663253222550238145794717339857336464086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree035.table
  base := (-1529234955116682330837815981200456437401/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-25601635087020984132573570361724869600000000000000)
      constant := (258696807794100105419951524495819242205849970495424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58187732321463612841/20000000000000000000)
  centralHi := (145469330803659032103/50000000000000000000)
  directionLo := (29518616601497104333/10000000000000000000)
  directionHi := (295186166014971043331/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree036.table
  base := (-6102818886465212234408197662767809395771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-19685808711016746812641837161934921200000000000000)
      constant := (204286172969104509281026393298568326117981155627932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree036.table
  base := (-6103550023560861303329502764520156006637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-26253792589540547032581282776174161600000000000000)
      constant := (272510466773261044752021624726659770039826327479472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29518616601497104333/10000000000000000000)
  centralHi := (295186166014971043331/100000000000000000000)
  directionLo := (299373412973461224421/100000000000000000000)
  directionHi := (149686706486730612211/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree037.table
  base := (-1516908910771147877098442426325235028211/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-20174800845374789447042229113877565200000000000000)
      constant := (214916687159557902151087105751158579290913782769648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree037.table
  base := (-6068306252152179390903252619964028757027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-26905950092060109932588995190623453600000000000000)
      constant := (286691449123239766446636841515325372114466913567312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299373412973461224421/100000000000000000000)
  centralHi := (149686706486730612211/50000000000000000000)
  directionLo := (303502896500410811071/100000000000000000000)
  directionHi := (4742232757818918923/1562500000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree038.table
  base := (-2404606115396070076702632176934486982643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-20663792979732832081442621065820209200000000000000)
      constant := (225821924769345346721845203005876851162356979910390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree038.table
  base := (-12024260045899240245628820177285484218837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-27558107594579672832596707605072745600000000000000)
      constant := (301238903887360432148012129299186288232247967021336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303502896500410811071/100000000000000000000)
  centralHi := (4742232757818918923/1562500000000000000)
  directionLo := (153788471587518217769/50000000000000000000)
  directionHi := (307576943175036435539/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree039.table
  base := (-2374111005629113813533567076250016060649/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-21152785114090874715843013017762853200000000000000)
      constant := (237001318102416639356138966566642654404574044256770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree039.table
  base := (-2374336285351904126676642866818756464459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-28210265097099235732604420019522037600000000000000)
      constant := (316152074427480276705386891643747402071552772410760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153788471587518217769/50000000000000000000)
  centralHi := (307576943175036435539/100000000000000000000)
  directionLo := (311597727465493734041/100000000000000000000)
  directionHi := (155798863732746867021/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree040.table
  base := (-11679303179158610399836540793033393704929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-21641777248448917350243404969705497200000000000000)
      constant := (248454362086302463024813262693325006190334214268234) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree040.table
  base := (-11680334589746799139531086552697655228333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-28862422599618798632612132433971329600000000000000)
      constant := (331430287589114396388335402889015043782488006798424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311597727465493734041/100000000000000000000)
  centralHi := (155798863732746867021/50000000000000000000)
  directionLo := (315567285298112966053/100000000000000000000)
  directionHi := (157783642649056483027/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree041.table
  base := (-11450573328111800340757770258801818708797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-22130769382806959984643796921648141200000000000000)
      constant := (260180607137960191206311815375592643110579828264162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree041.table
  base := (-11451517267588123295697677686202295206653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-29514580102138361532619844848420621600000000000000)
      constant := (347072944189243739144036386352432237471635913895384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315567285298112966053/100000000000000000000)
  centralHi := (157783642649056483027/50000000000000000000)
  directionLo := (4991992595451466647/1562500000000000000)
  directionHi := (319487526108893865409/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree042.table
  base := (-2796380413088927928160824925510131342887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-22619761517165002619044188873590785200000000000000)
      constant := (272179652888834898923162136291859310304789610589208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree042.table
  base := (-11186385103224449157510572649153820554067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-30166737604657924432627557262869913600000000000000)
      constant := (363079510649873486567325704534476225373039764388776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4991992595451466647/1562500000000000000)
  centralHi := (319487526108893865409/100000000000000000000)
  directionLo := (80840060894932244183/25000000000000000000)
  directionHi := (323360243579728976733/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree043.table
  base := (-2177035634707876586541383568563512289853/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-23108753651523045253444580825533429200000000000000)
      constant := (284451142656382197429357489986347444876806922243690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree043.table
  base := (-10885967614311387827212295507044460923553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-30818895107177487332635269677319205600000000000000)
      constant := (379449511626979249375805230626281716858588355398584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80840060894932244183/25000000000000000000)
  centralHi := (323360243579728976733/100000000000000000000)
  directionLo := (163593562615328915721/50000000000000000000)
  directionHi := (327187125230657831443/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree044.table
  base := (-10550460844836293276783093341214058299267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-23597745785881087887844972777476073200000000000000)
      constant := (296994758565852704539626670415783420496597559770782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree044.table
  base := (-263779556993070048236350787584880698659/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-31471052609697050232642982091768497600000000000000)
      constant := (396182523506553227834043508728014021805244391190080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163593562615328915721/50000000000000000000)
  centralHi := (327187125230657831443/100000000000000000000)
  directionLo := (330969761013695458273/100000000000000000000)
  directionHi := (165484880506847729137/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree045.table
  base := (-10182187998268929150695394227662450316149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-24086737920239130522245364729418717200000000000000)
      constant := (309810217239952158788233829257281025371069583854354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree045.table
  base := (-10182846986008597223527934260371206620759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-32123210112216613132650694506217789600000000000000)
      constant := (413278168657884567062814595602549402764128057468552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330969761013695458273/100000000000000000000)
  centralHi := (165484880506847729137/50000000000000000000)
  directionLo := (334709651032388370981/100000000000000000000)
  directionHi := (167354825516194185491/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree046.table
  base := (-2445272339152146587509856766256700181367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-24575730054597173156645756681361361200000000000000)
      constant := (322897265985569685101137055096206934961813058789528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree046.table
  base := (-9781691038316157286518984572442907586667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-32775367614736176032658406920667081600000000000000)
      constant := (430736110349648771853736366375254131819151182521576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334709651032388370981/100000000000000000000)
  centralHi := (167354825516194185491/50000000000000000000)
  directionLo := (67681642498681639867/20000000000000000000)
  directionHi := (42301026561676024917/12500000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree047.table
  base := (-934781578618358434418685966714652406709/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-25064722188955215791046148633304005200000000000000)
      constant := (336255679416512421729508471477240766282381745801140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree047.table
  base := (-292136403504267936968932040063233877511/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-33427525117255738932666119335116373600000000000000)
      constant := (448556048247377543392977905800752566787452606464256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67681642498681639867/20000000000000000000)
  centralHi := (42301026561676024917/12500000000000000000)
  directionLo := (17103339299077258913/5000000000000000000)
  directionHi := (342066785981545178261/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree048.table
  base := (-8882947943142770525644100519959725862239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-25553714323313258425446540585246649200000000000000)
      constant := (349885256459421591013609888033511503908353164189494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree048.table
  base := (-1110431112305800601217560804333878162627/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-34079682619775301832673831749565665600000000000000)
      constant := (466737714421864801290302711210007682122622515683648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17103339299077258913/5000000000000000000)
  centralHi := (342066785981545178261/100000000000000000000)
  directionLo := (345686641136889680179/100000000000000000000)
  directionHi := (17284332056844484009/5000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree049.table
  base := (-8387003945536772078252617096977851295397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-26042706457671301059846932537189293200000000000000)
      constant := (363785817697034687873472836895460530558377666347762) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree049.table
  base := (-8387460774627712455870262144510323617869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-34731840122294864732681544164014957600000000000000)
      constant := (485280869807385751023270088253052350273967590604632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345686641136889680179/100000000000000000000)
  centralHi := (17284332056844484009/5000000000000000000)
  directionLo := (349268981802371428491/100000000000000000000)
  directionHi := (87317245450592857123/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree050.table
  base := (-78604461863848411108404827582528649743/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-26531698592029343694247324489131937200000000000000)
      constant := (377957203008912721142599222443583586152708851867800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree050.table
  base := (-7860862616351441643125200427906081810761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-35383997624814427632689256578464249600000000000000)
      constant := (504185301056546297767189483499437682046290232358008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349268981802371428491/100000000000000000000)
  centralHi := (87317245450592857123/25000000000000000000)
  directionLo := (352814950700825289817/100000000000000000000)
  directionHi := (176407475350412644909/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree051.table
  base := (-18259218470481274258531836986824857493/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-27020690726387386328647716441074581200000000000000)
      constant := (392399269474842764121620856012261499351877480071200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree051.table
  base := (-7304066850903862464649904449831092139269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-36036155127333990532696968992913541600000000000000)
      constant := (523450817745369781104139171163516203788860351783832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352814950700825289817/100000000000000000000)
  centralHi := (176407475350412644909/50000000000000000000)
  directionLo := (71265126738619161809/20000000000000000000)
  directionHi := (178162816846547904523/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree052.table
  base := (-6717095986768240775822491593579150312313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-27509682860745428963048108393017225200000000000000)
      constant := (407111889510495177562831315034358949270016138691898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree052.table
  base := (-6717441639816415766330776680171556435101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-36688312629853553432704681407362833600000000000000)
      constant := (543077249888054571887408800847802936013903991437528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71265126738619161809/20000000000000000000)
  centralHi := (178162816846547904523/50000000000000000000)
  directionLo := (359802063662156905713/100000000000000000000)
  directionHi := (179901031831078452857/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree053.table
  base := (-1525250230330715667124322906134041445061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-27998674995103471597448500344959869200000000000000)
      constant := (422094949208677062161821242369242581357203161985224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree053.table
  base := (-3050657833896412303176673953856996663613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-37340470132373116332712393821812125600000000000000)
      constant := (563064445725853288385775568377688936722713662404528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359802063662156905713/100000000000000000000)
  centralHi := (179901031831078452857/50000000000000000000)
  directionLo := (2837853312989265191/781250000000000000)
  directionHi := (363245224062625944449/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree054.table
  base := (-1363923974612493189959804866134323110559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-28487667129461514231848892296902513200000000000000)
      constant := (437348346862773604663320083962557033049417095728856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree054.table
  base := (-545598240553991400847784063283048340663/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-37992627634892679232720106236261417600000000000000)
      constant := (583412269758858704851137616158634390624016342946640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2837853312989265191/781250000000000000)
  centralHi := (363245224062625944449/100000000000000000000)
  directionLo := (366656052170242843839/100000000000000000000)
  directionHi := (1145800163032008887/312500000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree055.table
  base := (-4781443189452613779971151880220035758283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-28976659263819556866249284248845157200000000000000)
      constant := (452871991651785288440903109834504417077510978801518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree055.table
  base := (-4781703905974105832040679598469970720669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-38644785137412242132727818650710709600000000000000)
      constant := (604120600993237237171444681100941095934874276643032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366656052170242843839/100000000000000000000)
  centralHi := (1145800163032008887/312500000000000000)
  directionLo := (185017721030870687263/50000000000000000000)
  directionHi := (370035442061741374527/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree056.table
  base := (-1019619253353497859090241215273644690027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-29465651398177599500649676200787801200000000000000)
      constant := (468665802468816331059178707889765510962538484022968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree056.table
  base := (-4078714186206628238389738083298178898471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-39296942639931805032735531065160001600000000000000)
      constant := (625189331379714721981925970007128376272787801850888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185017721030870687263/50000000000000000000)
  centralHi := (370035442061741374527/100000000000000000000)
  directionLo := (23336515459497435133/6250000000000000000)
  directionHi := (373384247351958962129/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree057.table
  base := (-3347006552251895990028819455194242526069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-29954643532535642135050068152730445200000000000000)
      constant := (484729706877002180009142472136507932274431563430674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree057.table
  base := (-3347222241551161586322243041885555822073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-39949100142451367932743243479609293600000000000000)
      constant := (646618364421963056630398363641021005650740381201144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23336515459497435133/6250000000000000000)
  centralHi := (373384247351958962129/100000000000000000000)
  directionLo := (188351641855964046183/50000000000000000000)
  directionHi := (376703283711928092367/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree058.table
  base := (-1293609319308774574731480606533339095957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-30443635666893684769450460104673089200000000000000)
      constant := (501063640178726552306594186322351257143362969467044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree058.table
  base := (-2587414732417651901221530435549285169461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-40601257644970930832750955894058585600000000000000)
      constant := (668407613936020291256246676134972039128576748291608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188351641855964046183/50000000000000000000)
  centralHi := (376703283711928092367/100000000000000000000)
  directionLo := (379993331188995873947/100000000000000000000)
  directionHi := (94998332797248968487/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree059.table
  base := (-1799280152790548877781761310391207538951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-30932627801251727403850852056615733200000000000000)
      constant := (517667544585609183444339966910613682188558591330246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree059.table
  base := (-1799458380246070603755413468103386514163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-41253415147490493732758668308507877600000000000000)
      constant := (690557002944051421223305041693937295221492098602664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (379993331188995873947/100000000000000000000)
  centralHi := (94998332797248968487/25000000000000000000)
  directionLo := (191627568173834541829/50000000000000000000)
  directionHi := (383255136347669083659/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree060.table
  base := (-196668032118079111538043315598223243727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-31421619935609770038251244008558377200000000000000)
      constant := (534541368478176026030801257620668173921146997129710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree060.table
  base := (-983502104501937029358321602429493098143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-41905572650010056632766380722957169600000000000000)
      constant := (713066462687664918176992093480297566733368782060104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191627568173834541829/50000000000000000000)
  centralHi := (383255136347669083659/100000000000000000000)
  directionLo := (48311176780978781791/12500000000000000000)
  directionHi := (386489414247830254329/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree061.table
  base := (-139531820693930332527831907729754479673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-31910612069967812672651635960501021200000000000000)
      constant := (551685065745381057414529715585395719330943421750458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree061.table
  base := (-69839464561805761332647662631874984343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-42557730152529619532774093137406461600000000000000)
      constant := (735935931747676899559550650034988462061468152027408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48311176780978781791/12500000000000000000)
  centralHi := (386489414247830254329/100000000000000000000)
  directionLo := (38969685027517408867/10000000000000000000)
  directionHi := (389696850275174088671/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree062.table
  base := (366012956724582714975542169283090085219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-32399604204325855307052027912443665200000000000000)
      constant := (569098595195255996367255831418956802375546090646852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree062.table
  base := (731892316386366922456070501095658194601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-43209887655049182432781805551855753600000000000000)
      constant := (759165355258691278954736528464178172321339229646472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38969685027517408867/10000000000000000000)
  centralHi := (389696850275174088671/100000000000000000000)
  directionLo := (392878101837137223233/100000000000000000000)
  directionHi := (196439050918568611617/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree063.table
  base := (1631226774730171316391757481080113438457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-32888596338683897941452419864386309200000000000000)
      constant := (586781920028940587264561565953508756172521021761478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree063.table
  base := (815552739426797341490301484430776923569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-43862045157568745332789517966305045600000000000000)
      constant := (782754684208166262930306875595900709914873968091536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392878101837137223233/100000000000000000000)
  centralHi := (196439050918568611617/50000000000000000000)
  directionLo := (198016899968104037061/50000000000000000000)
  directionHi := (396033799936208074123/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree064.table
  base := (319746978330223260430085031744120950979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-33377588473041940575852811816328953200000000000000)
      constant := (604735007371208361613776242089494005435693005907728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree064.table
  base := (511573145285167554138891157685237437431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-44514202660088308232797230380754337600000000000000)
      constant := (806703874810787403006585890596383641869040185731160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198016899968104037061/50000000000000000000)
  centralHi := (396033799936208074123/100000000000000000000)
  directionLo := (199582275315640816281/50000000000000000000)
  directionHi := (399164550631281632563/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree065.table
  base := (3512188253004413483036161235350586321253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-33866580607399983210253203768271597200000000000000)
      constant := (622957827851365245203006872331203381984007606206862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree065.table
  base := (3512088338988975006641035939806790555517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-45166360162607871132804942795203629600000000000000)
      constant := (831012887949984163852390669443212323178787562755624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199582275315640816281/50000000000000000000)
  centralHi := (399164550631281632563/100000000000000000000)
  directionLo := (40227093639664488389/10000000000000000000)
  directionHi := (402270936396644883891/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree066.table
  base := (2246894138713341331184069382308594978139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-34355572741758025844653595720214241200000000000000)
      constant := (641450355229073373303434904490647044577403923658212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree066.table
  base := (561712203534314780114695604396686823627/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-45818517665127434032812655209652921600000000000000)
      constant := (855681688679327073252560073947151109821358050652352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40227093639664488389/10000000000000000000)
  centralHi := (402270936396644883891/100000000000000000000)
  directionLo := (50669189673402925909/12500000000000000000)
  directionHi := (405353517387223407273/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree067.table
  base := (2751354099248016226757248192508429662869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-34844564876116068479053987672156885200000000000000)
      constant := (660212566060250659317162490311846867346126642953052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree067.table
  base := (343914123353499284562691039706155063313/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-46470675167646996932820367624102213600000000000000)
      constant := (880710245777340183681903490749732781412107824258176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50669189673402925909/12500000000000000000)
  centralHi := (405353517387223407273/100000000000000000000)
  directionLo := (204206416308936375661/50000000000000000000)
  directionHi := (408412832617872751323/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree068.table
  base := (6538887528227460460469070972899494626477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-35333557010474111113454379624099529200000000000000)
      constant := (679244439398727267159295151804568493692594774842558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree068.table
  base := (204337905036370006555847879715114749979/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-47122832670166559832828080038551505600000000000000)
      constant := (906098531349971113732541421717547436457528511337216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204206416308936375661/50000000000000000000)
  centralHi := (408412832617872751323/100000000000000000000)
  directionLo := (102862350265936424749/25000000000000000000)
  directionHi := (411449401063745698997/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree069.table
  base := (475142013916177112971332152168944243763/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-35822549144832153747854771576042173200000000000000)
      constant := (698545956529811189726033186268175882577542414182432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree069.table
  base := (475137788413063803204057886879615053923/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-47774990172686122732835792453000797600000000000000)
      constant := (931846520475589053570651978597214306784037641792896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102862350265936424749/25000000000000000000)
  centralHi := (411449401063745698997/100000000000000000000)
  directionLo := (207231861344048381791/50000000000000000000)
  directionHi := (414463722688096763583/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree070.table
  base := (271650437334052355563318550682735995149/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-36311541279190196382255163527984817200000000000000)
      constant := (718117100732333628854924663609694759656905869172672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree070.table
  base := (1086594088614229944590314635576259858109/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-48427147675205685632843504867450089600000000000000)
      constant := (957954190887939139911645802611486536577035826725184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207231861344048381791/50000000000000000000)
  centralHi := (414463722688096763583/100000000000000000000)
  directionLo := (41745627940328804153/10000000000000000000)
  directionHi := (417456279403288041531/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree071.table
  base := (981046970033472148660053547239910294139/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48772740000000000000000000000000000000000000000
      center := (282909391)
      previous := (0)
      next := (248713475)
      square := (6470976424493205492951552812532000000000000000)
      linear := (-518317372021806183333176837745457200000000000000)
      constant := (10393772634734041072621465498387039062399364970860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree071.table
  base := (9810414156823233602708588511723974809827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65030320000000000000000000000000000000000000000
      center := (377309713)
      previous := (0)
      next := (331520775)
      square := (8627968565990940657268737083376000000000000000)
      linear := (-691257819404580965251425595519709600000000000000)
      constant := (13865091868915178616011091668530127733355498895464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41745627940328804153/10000000000000000000)
  centralHi := (417456279403288041531/100000000000000000000)
  directionLo := (420427535970227106057/100000000000000000000)
  directionHi := (210213767985113553029/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree072.table
  base := (219104015810384865377563180852621099423/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-37289525547906281651055947431870105200000000000000)
      constant := (758068212182138658790171609109925429256238605802100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree072.table
  base := (5477575230562616837338363161830100588977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-49731462680244811432858929696348673600000000000000)
      constant := (1011248498115953983392355644994816405022453751513488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420427535970227106057/100000000000000000000)
  centralHi := (210213767985113553029/50000000000000000000)
  directionLo := (423377940840990347781/100000000000000000000)
  directionHi := (211688970420495173891/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree073.table
  base := (2425394564278737957122467611285963366773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-37778517682264324285456339383812749200000000000000)
      constant := (778448154152960333652823221509767726771268617964710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree073.table
  base := (12126927225359985368707774513728895113583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-50383620182764374332866642110797965600000000000000)
      constant := (1038435101275497227365164281217379300591627445739576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423377940840990347781/100000000000000000000)
  centralHi := (211688970420495173891/50000000000000000000)
  directionLo := (213153963474478723043/50000000000000000000)
  directionHi := (426307926948957446087/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree074.table
  base := (333143875422564046620351057377396482391/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-38267509816622366919856731335755393200000000000000)
      constant := (799097672321250813828610870183674361505570113260560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree074.table
  base := (1665714214594251453431601249902922489391/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-51035777685283937232874354525247257600000000000000)
      constant := (1065981317981816548381293799513288764046272661434816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213153963474478723043/50000000000000000000)
  centralHi := (426307926948957446087/100000000000000000000)
  directionLo := (42921791245039873557/10000000000000000000)
  directionHi := (429217912450398735571/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree075.table
  base := (2910303975603411012660179116322257836343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-38756501950980409554257123287698037200000000000000)
      constant := (820016757164468926183045485610011730937104648988610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree075.table
  base := (14551482475790992521344747883900642170387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-51687935187803500132882066939696549600000000000000)
      constant := (1093887135556433899796025112437428860670674904050264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42921791245039873557/10000000000000000000)
  centralHi := (429217912450398735571/100000000000000000000)
  directionLo := (3375846104852438283/781250000000000000)
  directionHi := (17284332056844484009/4000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree076.table
  base := (7902121416821086146594218517863601693873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-39245494085338452188657515239640681200000000000000)
      constant := (841205400173977313277423231468856723772479349392684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree076.table
  base := (790210448371572638399086334619356621171/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-52340092690323063032889779354145841600000000000000)
      constant := (1122152542671146856748606767705391170776179384470240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3375846104852438283/781250000000000000)
  centralHi := (17284332056844484009/4000000000000000000)
  directionLo := (217489742255697650803/50000000000000000000)
  directionHi := (434979484511395301607/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree077.table
  base := (3416780385748975058472246608027367983103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-39734486219696494823057907191583325200000000000000)
      constant := (862663593747045436839109831714199788369109348933810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree077.table
  base := (21354839086911949555812449264921329383/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-52992250192842625932897491768595133600000000000000)
      constant := (1150777529204165893259804468568435705773738749740800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217489742255697650803/50000000000000000000)
  centralHi := (434979484511395301607/100000000000000000000)
  directionLo := (437831839562359489991/100000000000000000000)
  directionHi := (54728979945294936249/12500000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree078.table
  base := (1149404846607977969257052726476761525467/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-40223478354054537457458299143525969200000000000000)
      constant := (884391331090365016861862269145446054192921569984288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree078.table
  base := (18390449794472974838273672573014374156717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-53644407695362188832905204183044425600000000000000)
      constant := (1179762086111591250714840413122465239423678360282024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437831839562359489991/100000000000000000000)
  centralHi := (54728979945294936249/12500000000000000000)
  directionLo := (440665732186336695043/100000000000000000000)
  directionHi := (110166433046584173761/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree079.table
  base := (3944790431099595739266175340268387580569/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-40712470488412580091858691095468613200000000000000)
      constant := (906388606133848766135288189130071927517864391561630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree079.table
  base := (2465490880062221829432831030438584404709/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-54296565197881751732912916597493717600000000000000)
      constant := (1209106205312591238596599386852816145871721392126784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440665732186336695043/100000000000000000000)
  centralHi := (110166433046584173761/25000000000000000000)
  directionLo := (221740758156952694601/50000000000000000000)
  directionHi := (443481516313905389203/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree080.table
  base := (1054215504753221267020119980705002680083/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-41201462622770622726259083047411257200000000000000)
      constant := (928655413453614918651678409126989851962928769913640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree080.table
  base := (10542143684755263446772686490334267823871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-54948722700401314632920629011943009600000000000000)
      constant := (1238809879586819294321914269123616791678438893715824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221740758156952694601/50000000000000000000)
  centralHi := (443481516313905389203/100000000000000000000)
  directionLo := (111569883677462790327/25000000000000000000)
  directionHi := (446279534709851161309/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree081.table
  base := (11235768684414541072967790802892605512601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-41690454757128665360659474999353901200000000000000)
      constant := (951191748203177504176810155977095821811558905213708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree081.table
  base := (1123575840429436148984754221939668787457/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-55600880202920877532928341426392301600000000000000)
      constant := (1268873102482763701182457103229542675685812378866080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111569883677462790327/25000000000000000000)
  centralHi := (446279534709851161309/100000000000000000000)
  directionLo := (56132514932523979579/12500000000000000000)
  directionHi := (449060119460191836633/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree082.table
  base := (3732128354851403937799885513933824413/1562500000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-42179446891486707995059866951296545200000000000000)
      constant := (973997606051967137102489405126906102938472969612800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree082.table
  base := (23885602872633376189062651030922007634937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-56253037705440440432936053840841593600000000000000)
      constant := (1299295868235863584584874088660956221365951013657864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56132514932523979579/12500000000000000000)
  centralHi := (449060119460191836633/100000000000000000000)
  directionLo := (451823592432226007423/100000000000000000000)
  directionHi := (3529871815876765683/781250000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree083.table
  base := (6331637806802281384820157348011452959013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-42668439025844750629460258903239189200000000000000)
      constant := (997072983130400639803037731552566355586257676439608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree083.table
  base := (12663267202958842265668597123913961712341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-56905195207960003332943766255290885600000000000000)
      constant := (1330078171695349509790518696782410957123222221143504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451823592432226007423/100000000000000000000)
  centralHi := (3529871815876765683/781250000000000000)
  directionLo := (454570265709409103933/100000000000000000000)
  directionHi := (227285132854704551967/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree084.table
  base := (26794316652290911055458425469104355525321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-43157431160202793263860650855181833200000000000000)
      constant := (1020417875980801330895186798289863210630818716301734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree084.table
  base := (26794301440516744194410095655121598613761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-57557352710479566232951478669740177600000000000000)
      constant := (1361220008258878318560209359939928509497027483057992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454570265709409103933/100000000000000000000)
  centralHi := (227285132854704551967/50000000000000000000)
  directionLo := (228650221001360126519/50000000000000000000)
  directionHi := (457300442002720253039/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree085.table
  base := (14144454412067606876551142367067521116469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-43646423294560835898261042807124477200000000000000)
      constant := (1044032281513546363921002024043652368531984342021852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree085.table
  base := (707222376745463241373563812409495000317/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-58209510212999129132959191084189469600000000000000)
      constant := (1392721373814131216930966760470672575628160149648960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228650221001360126519/50000000000000000000)
  centralHi := (457300442002720253039/100000000000000000000)
  directionLo := (230007207520027416111/50000000000000000000)
  directionHi := (460014415040054832223/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree086.table
  base := (29810319770291371437114936517529484568889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-44135415428918878532661434759067121200000000000000)
      constant := (1067916196967884069378991318768676935251808290529606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree086.table
  base := (5962061467101704244249571016645798555631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-58861667715518692032966903498638761600000000000000)
      constant := (1424582264686632851781794413072090733638851871483160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230007207520027416111/50000000000000000000)
  centralHi := (460014415040054832223/100000000000000000000)
  directionLo := (231356234967530289931/50000000000000000000)
  directionHi := (462712469935060579863/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree087.table
  base := (6271708473383033167106347649963226222357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-44624407563276921167061826711009765200000000000000)
      constant := (1092069619876923694075354038776177158594699105260390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree087.table
  base := (391981639082399356358627423499709318733/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-59513825218038254932974615913088053600000000000000)
      constant := (1456802677593128338513972650323470558851579343230080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231356234967530289931/50000000000000000000)
  centralHi := (462712469935060579863/100000000000000000000)
  directionLo := (465394883536728255481/100000000000000000000)
  directionHi := (232697441768364127741/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree088.table
  base := (3293357024843208833645586415866586273869/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-45113399697634963801462218662952409200000000000000)
      constant := (1116492548036353013750083970055597376578631688705260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree088.table
  base := (16466780044585422495800012086395724713123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-60165982720557817832982328327537345600000000000000)
      constant := (1489382609599925949252855063405149127871113415828912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465394883536728255481/100000000000000000000)
  centralHi := (232697441768364127741/50000000000000000000)
  directionLo := (93612384952190032793/20000000000000000000)
  directionHi := (234030962380475081983/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree089.table
  base := (34535397726819104693580111652240379168869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-45602391831993006435862610614895053200000000000000)
      constant := (1141184979476486701603706828826750294858003113200526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree089.table
  base := (17267694272914974526479667882449231875557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-60818140223077380732990040741986637600000000000000)
      constant := (1522322058085676352223989021910223863893227740813008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93612384952190032793/20000000000000000000)
  centralHi := (234030962380475081983/50000000000000000000)
  directionLo := (117678463726292620171/25000000000000000000)
  directionHi := (94142770981034096137/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree090.table
  base := (36164019719480401253796209860619425540489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-46091383966351049070263002566837697200000000000000)
      constant := (1166146912437290676211042965892019733113932969236006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree090.table
  base := (36164011423607701085658246142793724821277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-61470297725596943632997753156435929600000000000000)
      constant := (1555621020708115721087833573300084194495749061442344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117678463726292620171/25000000000000000000)
  centralHi := (94142770981034096137/20000000000000000000)
  directionLo := (473350927947169449079/100000000000000000000)
  directionHi := (11833773198679236227/2500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree091.table
  base := (4727428960600225864716351602058854296379/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-46580376100709091704663394518780341200000000000000)
      constant := (1191378345346065470825941103654263035228765991600528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree091.table
  base := (37819424189637743666156069997922790866319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-62122455228116506533005465570885221600000000000000)
      constant := (1589279495374350432686929410854424501669841592723768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473350927947169449079/100000000000000000000)
  centralHi := (11833773198679236227/2500000000000000000)
  directionLo := (475973390828948461067/100000000000000000000)
  directionHi := (118993347707237115267/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree092.table
  base := (19750814782283068446426253142386146966857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-47069368235067134339063786470722985200000000000000)
      constant := (1216879276797505446964732812994429202263751532110156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree092.table
  base := (493770284920547904738694650399912833013/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-62774612730636069433013177985334513600000000000000)
      constant := (1623297480214306089155901387700325600197671029962880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475973390828948461067/100000000000000000000)
  centralHi := (118993347707237115267/25000000000000000000)
  directionLo := (59822685465826767457/12500000000000000000)
  directionHi := (478581483726614139657/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree093.table
  base := (4121060973249884501587271449568961658509/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-47558360369425176973464178422665629200000000000000)
      constant := (1242649705535880850806073588030472033211870405370860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree093.table
  base := (20605301808279078591540115417435145707723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-63426770233155632333020890399783805600000000000000)
      constant := (1657674973557003812195041777695053581735601914891312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59822685465826767457/12500000000000000000)
  centralHi := (478581483726614139657/100000000000000000000)
  directionLo := (120293860076774063447/25000000000000000000)
  directionHi := (481175440307096253789/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree094.table
  base := (42946368948291215145530228753353585498513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-48047352503783219607864570374608273200000000000000)
      constant := (1268689630439116667172113521715345012530465889042902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree094.table
  base := (21473181712305436185462670672459499365411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-64078927735675195233028602814233097600000000000000)
      constant := (1692411973909362677908259762386835594716969134513584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120293860076774063447/25000000000000000000)
  centralHi := (481175440307096253789/100000000000000000000)
  directionLo := (24187774398623804851/5000000000000000000)
  directionHi := (483755487972476097021/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree095.table
  base := (44708904316517863127610664352817552559449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-48536344638141262242264962326550917200000000000000)
      constant := (1294999050504566306962501925613780329184770218403846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree095.table
  base := (4470889932830813139757510833310730581241/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-64731085238194758133036315228682389600000000000000)
      constant := (1727508479937259248995678645026322899558364064125520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24187774398623804851/5000000000000000000)
  centralHi := (483755487972476097021/100000000000000000000)
  directionLo := (486321848092648395009/100000000000000000000)
  directionHi := (48632184809264839501/10000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree096.table
  base := (46498213249927446542924636685357248435439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-49025336772499304876665354278493561200000000000000)
      constant := (1321577964836299677204157926175180678483905219243306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree096.table
  base := (9299641749155601695228532294081089359717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-65383242740714321033044027643131681600000000000000)
      constant := (1762964490448603826973442140246318788418890202490120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486321848092648395009/100000000000000000000)
  centralHi := (48632184809264839501/10000000000000000000)
  directionLo := (122218684056747614613/25000000000000000000)
  directionHi := (488874736226990458453/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree097.table
  base := (48314293436640982047286851535846624199779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-49514328906857347511065746230436205200000000000000)
      constant := (1348426372633744402677698536346843347782012057493666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree097.table
  base := (48314289370019153964218860139396677967413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-66035400243233883933051740057580973600000000000000)
      constant := (1798780004378218656187038208951366441533620500431336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122218684056747614613/25000000000000000000)
  centralHi := (488874736226990458453/100000000000000000000)
  directionLo := (61426795291958349453/12500000000000000000)
  directionHi := (786262979737066873/160000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree098.table
  base := (2507857140542087841952141493231638585351/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-50003321041215390145466138182378849200000000000000)
      constant := (1375544273181536139293102421248909606126615482707080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree098.table
  base := (12539284784909145578374035700697075804249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-66687557745753446833059452472030265600000000000000)
      constant := (1834955020774326190184593956226618023578253783162912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61426795291958349453/12500000000000000000)
  centralHi := (786262979737066873/160000000000000000)
  directionLo := (30871308186322212859/6250000000000000000)
  directionHi := (98788186196231081149/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree099.table
  base := (52026759526585123115029772495255377442917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-50492313175573432779866530134321493200000000000000)
      constant := (1402931665840449260682333445169848891279139315346318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree099.table
  base := (26013378106346630547931850785533606977221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-67339715248273009733067164886479557600000000000000)
      constant := (1871489538786475971031691379961227243671257383638224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30871308186322212859/6250000000000000000)
  centralHi := (98788186196231081149/20000000000000000000)
  directionLo := (49645464152054318741/10000000000000000000)
  directionHi := (496454641520543187411/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree100.table
  base := (26961570967198023086068118047269735031269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-50981305309931475414266922086264137200000000000000)
      constant := (1430588550039292906116524203630994101850995442260252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree100.table
  base := (53923138943345721105675055412546601304809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-67991872750792572633074877300928849600000000000000)
      constant := (1908383557654756933674621791229805986234125442343048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49645464152054318741/10000000000000000000)
  centralHi := (496454641520543187411/100000000000000000000)
  directionLo := (249477844144551020351/50000000000000000000)
  directionHi := (498955688289102040703/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree101.table
  base := (27923144280178820815005421820681540237941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-51470297444289518048667314038206781200000000000000)
      constant := (1458514925267669624212874831009683828064509810302428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree101.table
  base := (27923142930483622102489423772235474997547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-68644030253312135533082589715378141600000000000000)
      constant := (1945637076700158262937853645812635243623083224875568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249477844144551020351/50000000000000000000)
  centralHi := (498955688289102040703/100000000000000000000)
  directionLo := (250722130387812034341/50000000000000000000)
  directionHi := (501444260775624068683/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree102.table
  base := (5779619808742553480658177671463399546201/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-51959289578647560683067705990149425200000000000000)
      constant := (1486710791069504788702083299931546168596391534612540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree102.table
  base := (57796195651493757024196455918592278489783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-69296187755831698433090302129827433600000000000000)
      constant := (1983250095315956507760123993705323001920009907065976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250722130387812034341/50000000000000000000)
  centralHi := (501444260775624068683/100000000000000000000)
  directionLo := (503920543789963568609/100000000000000000000)
  directionHi := (50392054378996356861/10000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree103.table
  base := (5977286933873110723318675941259800178647/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-52448281713005603317468097942092069200000000000000)
      constant := (1515176147037264738870757640750993004566122361477380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree103.table
  base := (59772867140755766399627030954111121829741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-69948345258351261333098014544276725600000000000000)
      constant := (2021222612960019681231252556617039350183844003504552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503920543789963568609/100000000000000000000)
  centralHi := (50392054378996356861/10000000000000000000)
  directionLo := (126596179405801260269/25000000000000000000)
  directionHi := (506384717623205041077/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree104.table
  base := (772203765783274005153044456140486659421/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-52937273847363645951868489894034713200000000000000)
      constant := (1543910992806790332409277013651980152890016302650720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree104.table
  base := (1930509352487027349015060852596268485889/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-70600502760870824233105726958726017600000000000000)
      constant := (2059554629147930711481418356107516590724712569497856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126596179405801260269/25000000000000000000)
  centralHi := (506384717623205041077/100000000000000000000)
  directionLo := (127209239550212512683/25000000000000000000)
  directionHi := (508836958200850050733/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree105.table
  base := (1276129858390602913157224640112167259903/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-53426265981721688586268881845977357200000000000000)
      constant := (1572915328052680403255044766595390284134335312698100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree105.table
  base := (24924410597853880859496977314790024717/3906250000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-71252660263390387133113439373175309600000000000000)
      constant := (2098246143446843005405987812586798570315846727741440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127209239550212512683/25000000000000000000)
  centralHi := (508836958200850050733/100000000000000000000)
  directionLo := (127819359307347819223/25000000000000000000)
  directionHi := (511277437229391276893/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree106.table
  base := (65863443469659967478925050972464529452887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-53915258116079731220669273797920001200000000000000)
      constant := (1602189152484166590752084509496726858745018799292698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree106.table
  base := (13172688371169202494512763671566743095567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-71904817765909950033121151787624601600000000000000)
      constant := (2137297155469990176702728442740388395872619196996120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127819359307347819223/25000000000000000000)
  centralHi := (511277437229391276893/100000000000000000000)
  directionLo := (51370632233661934257/10000000000000000000)
  directionHi := (513706322336619342571/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree107.table
  base := (67947152162742922184996467003502120478927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32363220000000000000000000000000000000000000000
      center := (187724923)
      previous := (0)
      next := (165034175)
      square := (4293825477934743831771591118596000000000000000)
      linear := (-508450936919979194907193137849183600000000000000)
      constant := (15249836129359133061708846022638029189552601986494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree107.table
  base := (67947150707109321213111810787237382379997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43150960000000000000000000000000000000000000000
      center := (250364389)
      previous := (0)
      next := (219981075)
      square := (5725100637246325109028788158128000000000000000)
      linear := (-678102572602144980683447328991344800000000000000)
      constant := (20343062288521311119401689239665400229758395534712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51370632233661934257/10000000000000000000)
  centralHi := (513706322336619342571/100000000000000000000)
  directionLo := (64515472150748358353/12500000000000000000)
  directionHi := (20644951088239474673/4000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree108.table
  base := (70057618328326211663563642073298607780149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-54893242384795816489470057701805289200000000000000)
      constant := (1661545267892293621774571193949171148571324608801646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree108.table
  base := (35028808507741667489778748717587841147453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-73209132770949075833136576616523185600000000000000)
      constant := (2216477671343412387154728457305325303318578108004432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64515472150748358353/12500000000000000000)
  centralHi := (20644951088239474673/4000000000000000000)
  directionLo := (129632490426333630067/25000000000000000000)
  directionHi := (518529961705334520269/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree109.table
  base := (4512177585457087417453358948438940532521/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-55382234519153859123870449653747933200000000000000)
      constant := (1691627558429306762412987696367563289640377100328544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree109.table
  base := (7219484018335564801474532203641572127083/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-73861290273468638733144289030972477600000000000000)
      constant := (2256607174608959694364232125116457522301637459115760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129632490426333630067/25000000000000000000)
  centralHi := (518529961705334520269/100000000000000000000)
  directionLo := (130231258002566390317/25000000000000000000)
  directionHi := (520925032010265561269/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree110.table
  base := (7435882074436972691108843186299856160861/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-55871226653511901758270841605690577200000000000000)
      constant := (1721979337267087485048750357046280227706546092768940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree110.table
  base := (74358819676733972149047675849524062159547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-74513447775988201633152001445421769600000000000000)
      constant := (2297096174421869816826349758568833964430540150501784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130231258002566390317/25000000000000000000)
  centralHi := (520925032010265561269/100000000000000000000)
  directionLo := (261654570361219142253/50000000000000000000)
  directionHi := (523309140722438284507/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree111.table
  base := (76549555981135779168477125680658062777667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-56360218787869944392671233557633221200000000000000)
      constant := (1752600604239986403365422921020642738145787695822818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree111.table
  base := (38274777509236558861079182083867099190509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-75165605278507764533159713859871061600000000000000)
      constant := (2337944670561837533513581495370134971879193685506896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261654570361219142253/50000000000000000000)
  centralHi := (523309140722438284507/100000000000000000000)
  directionLo := (525682436983029927487/100000000000000000000)
  directionHi := (8213788077859842617/1562500000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree112.table
  base := (3150681866006537453869029356037616862981/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-56849210922227987027071625509575865200000000000000)
      constant := (1783491359199984023929271216858022540252307358984350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree112.table
  base := (19691761445555760731372831082585027033409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-75817762781027327433167426274320353600000000000000)
      constant := (2379152662832010518905064649663563620079431158088992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525682436983029927487/100000000000000000000)
  centralHi := (8213788077859842617/1562500000000000000)
  directionLo := (66005633322701345687/12500000000000000000)
  directionHi := (528045066581610765497/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree113.table
  base := (40505646184748628863796558269159877979319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-57338203056586029661472017461518509200000000000000)
      constant := (1814651602014814351587968307075914265009062123689652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree113.table
  base := (20252822896755300893366124706506816889419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-76469920283546890333175138688769645600000000000000)
      constant := (2420720151056492548290341183286963680569809150027872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66005633322701345687/12500000000000000000)
  centralHi := (528045066581610765497/100000000000000000000)
  directionLo := (530397172060653300423/100000000000000000000)
  directionHi := (66299646507581662553/12500000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree114.table
  base := (666258342382660691008661635328793547739/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-57827195190944072295872409413461153200000000000000)
      constant := (1846081332566288206957807721231953853018077253438250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree114.table
  base := (41641146046230304351147641530002615260793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-77122077786066453233182851103218937600000000000000)
      constant := (2462647135078112515245866668810983032731696781861392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530397172060653300423/100000000000000000000)
  centralHi := (66299646507581662553/12500000000000000000)
  directionLo := (532738892815888539413/100000000000000000000)
  directionHi := (266369446407944269707/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree115.table
  base := (85580047630188995431781117507608892032241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-58316187325302114930272801365403797200000000000000)
      constant := (1877780550748794999481890556982551379240713589563414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree115.table
  base := (85580046994372290501633510795954234779663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-77774235288586016133190563517668229600000000000000)
      constant := (2504933614756430962065126034816574081260843962113336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532738892815888539413/100000000000000000000)
  centralHi := (266369446407944269707/50000000000000000000)
  directionLo := (53507036519270929739/10000000000000000000)
  directionHi := (535070365192709297391/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree116.table
  base := (21976139148511056196504058791549166780761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-58805179459660157564673193317346441200000000000000)
      constant := (1909749256467963962071119091020317471724657288445976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree116.table
  base := (87904556020967422588763250123526510111537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-78426392791105579033198275932117521600000000000000)
      constant := (2547579589965958836848262818703017125815359056293064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53507036519270929739/10000000000000000000)
  centralHi := (535070365192709297391/100000000000000000000)
  directionLo := (268695861289404590271/50000000000000000000)
  directionHi := (537391722578809180543/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree117.table
  base := (45127909722939797920804117882744576177739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-59294171594018200199073585269289085200000000000000)
      constant := (1941987449639467875031310228513902784544644224095012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree117.table
  base := (9025581892939015134510112003100724301729/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-79078550293625141933205988346566813600000000000000)
      constant := (2590585060594565883084980610451808626093698153052880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268695861289404590271/50000000000000000000)
  centralHi := (537391722578809180543/100000000000000000000)
  directionLo := (53970309549323535857/10000000000000000000)
  directionHi := (539703095493235358571/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree118.table
  base := (46316917984046554405895454094359754097859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-59783163728376242833473977221231729200000000000000)
      constant := (1974495130187954113472995942088666748893719124203972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree118.table
  base := (92633835502637414937263363388120711457109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-79730707796144704833213700761016105600000000000000)
      constant := (2633950026542058473056045809959161387659252598268648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53970309549323535857/10000000000000000000)
  centralHi := (539703095493235358571/100000000000000000000)
  directionLo := (542004611672023358997/100000000000000000000)
  directionHi := (271002305836011679499/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree119.table
  base := (95038605966241088486182681036931773517703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-60272155862734285467874369173174373200000000000000)
      constant := (2007272298046089466604845493397917085691376478095162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree119.table
  base := (95038605546806679846280273686954434655537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-80382865298664267733221413175465397600000000000000)
      constant := (2677674487718908845756258202025014429298587492261064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542004611672023358997/100000000000000000000)
  centralHi := (271002305836011679499/50000000000000000000)
  directionLo := (272148198075286434367/50000000000000000000)
  directionHi := (108859279230114573747/20000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree120.table
  base := (1522970769790209526361998433777217554097/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-60761147997092328102274761125117017200000000000000)
      constant := (2040318953153706619697046237253204919538867411330432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree120.table
  base := (24367532222159171073483044242842351672687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-81035022801183830633229125589914689600000000000000)
      constant := (2721758444045119630576623886212957713822697332703456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272148198075286434367/50000000000000000000)
  centralHi := (108859279230114573747/20000000000000000000)
  directionLo := (109315714268582972323/20000000000000000000)
  directionHi := (34161160708932178851/6250000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree121.table
  base := (49964202856915527789165085253036965075059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-61250140131450370736675153077059661200000000000000)
      constant := (2073635095457041478357789242558296009933528049901572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree121.table
  base := (99928405373309994659366582495348497018869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-81687180303703393533236838004363981600000000000000)
      constant := (2766201895449209254042549009886316458885858289467368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109315714268582972323/20000000000000000000)
  centralHi := (34161160708932178851/6250000000000000000)
  directionLo := (137212814279503061193/25000000000000000000)
  directionHi := (548851257118012244773/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree122.table
  base := (102413435169278087762658991906498302155621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-61739132265808413371075545029002305200000000000000)
      constant := (2107220724908051666437211298595286193010490552257934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree122.table
  base := (102413434862489501976445723823125270153279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-82339337806222956433244550418813273600000000000000)
      constant := (2811004841867305360260039635425728294198894695176888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137212814279503061193/25000000000000000000)
  centralHi := (548851257118012244773/100000000000000000000)
  directionLo := (551114570873228593479/100000000000000000000)
  directionHi := (13777864271830714837/2500000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree123.table
  base := (104925217508943078892466808270441932856113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-62228124400166456005475936980944949200000000000000)
      constant := (2141075841463807557961763056603466813541649462993302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree123.table
  base := (13115652154070494128170896298225999563199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-82991495308742519333252262833262565600000000000000)
      constant := (2856167283242334745826453807814816260096354459801024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551114570873228593479/100000000000000000000)
  centralHi := (13777864271830714837/2500000000000000000)
  directionLo := (4426949020840739109/800000000000000000)
  directionHi := (276684313802546194313/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree124.table
  base := (21492750524409542797221723946357795789179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-62717116534524498639876328932887593200000000000000)
      constant := (2175200445085948123056355594492370141395454637406330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree124.table
  base := (21492750474616052405403635230070353764429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-83643652811262082233259975247711857600000000000000)
      constant := (2901689219523299534198049153600266106237397798298440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4426949020840739109/800000000000000000)
  centralHi := (276684313802546194313/50000000000000000000)
  directionLo := (55561353997747745093/10000000000000000000)
  directionHi := (555613539977477450931/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree125.table
  base := (1100290404096026394780544106881777710933/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-63206108668882541274276720884830237200000000000000)
      constant := (2209594535740194689491029266528489680073522560158200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree125.table
  base := (13753630023167839769065453762790476805411/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-84295810313781645133267687662161149600000000000000)
      constant := (2947570650664630408404238255446018809067760247494336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55561353997747745093/10000000000000000000)
  centralHi := (555613539977477450931/100000000000000000000)
  directionLo := (139462354596828487909/25000000000000000000)
  directionHi := (557849418387313951637/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree126.table
  base := (112621080783152759303707271980191319817507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-63695100803240583908677112836772881200000000000000)
      constant := (2244258113395916455711345454099650799581184426150178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree126.table
  base := (112621080581161321029000711554244005676767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-84947967816301208033275400076610441600000000000000)
      constant := (2993811576625608698435175420374227254435418019485624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139462354596828487909/25000000000000000000)
  centralHi := (557849418387313951637/100000000000000000000)
  directionLo := (70009546378492305399/12500000000000000000)
  directionHi := (560076371027938443193/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree127.table
  base := (14404984207957008990129251721482272927517/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-64184092937598626543077504788715525200000000000000)
      constant := (2279191178025742247286250951947246107727440487637744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree127.table
  base := (115239873481733368010809190488909136077849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-85600125318820770933283112491059733600000000000000)
      constant := (3040411997369849993004493749968355899197469064209928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70009546378492305399/12500000000000000000)
  centralHi := (560076371027938443193/100000000000000000000)
  directionLo := (281147251975092884929/50000000000000000000)
  directionHi := (562294503950185769859/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree128.table
  base := (29471354745120458779596491876218941904801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-64673085071956669177477896740658169200000000000000)
      constant := (2314393729605213594951885825142399706879382175462616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree128.table
  base := (29471354704161026797320384588837413117819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-86252282821340333833290824905509025600000000000000)
      constant := (3087371912864842725781870297125926070245880670527072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell152.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281147251975092884929/50000000000000000000)
  centralHi := (562294503950185769859/100000000000000000000)
  directionLo := (141125980280330115927/25000000000000000000)
  directionHi := (564503921121320463709/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree129.table
  base := (15069714583814419776959158169418625007887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3462864540000000000000000000000000000000000000000
      center := (20086566761)
      previous := (0)
      next := (17658656725)
      square := (459439326139017589999560249689772000000000000000)
      linear := (-65162077206314711811878288692600813200000000000000)
      constant := (2349865768112474736277334904955046275964295290101584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 32351
  qDenominator := 60776
  table := BinomialMassData.Q32351_60776.Degree129.table
  base := (7534857282685861273361052459251202321963/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4617152720000000000000000000000000000000000000000
      center := (26788989623)
      previous := (0)
      next := (23537975025)
      square := (612585768185356786666080332919696000000000000000)
      linear := (-86904440323859896733298537319958317600000000000000)
      constant := (3134691323081535883500139063551450850392594849902976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q32351_60776.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell152.Kernel129
