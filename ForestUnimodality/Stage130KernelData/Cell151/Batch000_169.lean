import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell151.Parameters
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch100_149
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch150_199
import ForestUnimodality.BinomialMassData.Q47737_90312.Batch000_049
import ForestUnimodality.BinomialMassData.Q47737_90312.Batch050_099
import ForestUnimodality.BinomialMassData.Q47737_90312.Batch100_149
import ForestUnimodality.BinomialMassData.Q47737_90312.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree000.table
  base := (679322276224484257645030999/10000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (182766280420646777538085102500000000000)
      linear := (-13310336541699787325787607250000000000)
      constant := (169830569056121064411257749750000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree000.table
  base := (679322276224484257645030999/10000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (182766280420646777538085102500000000000)
      linear := (-13310336541699787325787607250000000000)
      constant := (169830569056121064411257749750000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree001.table
  base := (380764076669704722349611222773617015573947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-11694740340778043575709274550610862250000000000)
      constant := (5394972858071096414953014559992022101904284017043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree001.table
  base := (380686215340183173889815837067204800142997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-35092817891249416899926271329841430500000000000)
      constant := (16181615842028892749269040255584569708251935059479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24959129473215556711/50000000000000000000)
  directionHi := (49918258946431113423/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree002.table
  base := (56883190467771915625708233762350945009441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-16976680666535031756172280095619417625000000000)
      constant := (2425696728917104731620794738176587796766110966587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree002.table
  base := (113726579944211734444103859999082983920981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-11320652733995116561714335956415893000000000000)
      constant := (1616570697213195915402114262053491964282873605789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24959129473215556711/50000000000000000000)
  centralHi := (49918258946431113423/100000000000000000000)
  directionLo := (35297539406047483679/50000000000000000000)
  directionHi := (70595078812094967359/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree003.table
  base := (145778440316419233935290249004166671812603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-33576408103315374440750139037707584750000000000)
      constant := (2091459633813895110138864241797821080073057309907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree003.table
  base := (145715174867983847883741738402713930775731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-33585004972230660613548586715716428500000000000)
      constant := (2090577727995353029086469313280724994719902058539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35297539406047483679/50000000000000000000)
  centralHi := (70595078812094967359/100000000000000000000)
  directionLo := (4323048036029917191/5000000000000000000)
  directionHi := (86460960720598343821/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree004.table
  base := (6239334449849698706298267066915628246763/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-11129310496146009968317642820313986500000000000)
      constant := (365361670568507491311147649611529860330101131788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree004.table
  base := (12472808770482058189688096601700539142213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-33396528357353316077751376138950803250000000000)
      constant := (1095605616335105488496245268557032081619106683982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4323048036029917191/5000000000000000000)
  centralHi := (86460960720598343821/100000000000000000000)
  directionLo := (19967303578572445369/20000000000000000000)
  directionHi := (49918258946431113423/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree005.table
  base := (18078859581936207001772371857241500704517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-41593556899389528979343252643603230437500000000)
      constant := (823695389593219948062128780126412253585536225119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree005.table
  base := (36140465252603398487486570903788181616117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-27736201990355757796894208160742856750000000000)
      constant := (548905133660128527560726337518702247902534843773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19967303578572445369/20000000000000000000)
  centralHi := (49918258946431113423/50000000000000000000)
  directionLo := (22324124064531400529/20000000000000000000)
  directionHi := (55810310161328501323/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree006.table
  base := (54669586370257027053706622817756169708307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-66398909747121370738311435768352668500000000000)
      constant := (880589344355779192881171063763772298143557823883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree006.table
  base := (54643627837161644872009672064443288912747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-66416103484951943083908331124370356000000000000)
      constant := (880276915547856491936105970768674067295323774243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22324124064531400529/20000000000000000000)
  centralHi := (55810310161328501323/50000000000000000000)
  directionLo := (24454852653375525389/20000000000000000000)
  directionHi := (61137131633438813473/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree007.table
  base := (5322824048913993363770922449929993700917/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-19334935907097509042707967002975257437500000000)
      constant := (186853528792575787484284204812251807910730974946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree007.table
  base := (2128121739002212491771286777687073212689/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-58019852241894277930521184445441248875000000000)
      constant := (560402716019891662756701402610262048879175266615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24454852653375525389/20000000000000000000)
  centralHi := (61137131633438813473/50000000000000000000)
  directionLo := (132071299053581846931/100000000000000000000)
  directionHi := (33017824763395461733/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree008.table
  base := (8455731512185432916087951599192511239307/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-66210433132244026202514225191587043250000000000)
      constant := (500351988845605351875600985137987487798959688649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree008.table
  base := (676135772824205018736954231156293984227/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-44151751246716399032074080365069820500000000000)
      constant := (333502620031657511348586504334258777258441359075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132071299053581846931/100000000000000000000)
  centralHi := (33017824763395461733/25000000000000000000)
  directionLo := (141190157624189934717/100000000000000000000)
  directionHi := (70595078812094967359/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree009.table
  base := (424798943298035333502795469849302475607/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-24805352847731841758968183124749438062500000000)
      constant := (155678457111838938244805600506770514819056586328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree009.table
  base := (27173904408795054406240208129359655130657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-99247201997673225554268075533024283500000000000)
      constant := (622650132619565256100771100378124165713070201033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141190157624189934717/100000000000000000000)
  centralHi := (70595078812094967359/50000000000000000000)
  directionLo := (37438694209823335067/25000000000000000000)
  directionHi := (149754776839293340269/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree010.table
  base := (21991446461759959825000840523482967771043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-110162245272196032468393164742546113500000000000)
      constant := (604465418638539486569021461922182134290772186267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree010.table
  base := (21980432608493249515802160400193380693481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-330572704505740959133163971007726778000000000000)
      constant := (1813385864959141431098960205087207755528084474867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37438694209823335067/25000000000000000000)
  centralHi := (149754776839293340269/100000000000000000000)
  directionLo := (157855395100799449801/100000000000000000000)
  directionHi := (78927697550399724901/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree011.table
  base := (17823145829553334744431199237166403264967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-363309237460394093702740790958283424250000000000)
      constant := (1819639606424663432791793540617256267804440998269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree011.table
  base := (17813894263883181338654397718752490594419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-121134601006154080534507905138793568500000000000)
      constant := (606599935148683036469528213615375162769133496811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157855395100799449801/100000000000000000000)
  centralHi := (78927697550399724901/50000000000000000000)
  directionLo := (82780067556556827251/50000000000000000000)
  directionHi := (165560135113113654503/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree012.table
  base := (1802134202374050682566493830645814493869/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-33010978258683340833358507307410709000000000000)
      constant := (156300628267887626774845121432958720095419007722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree012.table
  base := (7204635968736192230608374458480011465429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-66039150255197254012313909970839105500000000000)
      constant := (312655690701816343963722708674072356472412297501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82780067556556827251/50000000000000000000)
  centralHi := (165560135113113654503/100000000000000000000)
  directionLo := (172921921441196687641/100000000000000000000)
  directionHi := (86460960720598343821/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree013.table
  base := (579644343919291082132293766365027233587/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-35746186729000507191488615368297799312500000000)
      constant := (164469916188654804638764317610140149689487606015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree013.table
  base := (1158630305975979895879990376615053133303/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-214533000021952403272121602116844280250000000000)
      constant := (987065617954080265791015661344069805970125123105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172921921441196687641/100000000000000000000)
  centralHi := (86460960720598343821/50000000000000000000)
  directionLo := (179982842213246395383/100000000000000000000)
  directionHi := (22497855276655799423/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree014.table
  base := (4611039890673217134999095702144752996027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-230888371195906041297712340575109337750000000000)
      constant := (1054137489457450883602909167974801861207870945689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree014.table
  base := (921653014519172442323141417906525751917/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-76982849759437681502433824773723748000000000000)
      constant := (351489023570595023957066219099884935937483969865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179982842213246395383/100000000000000000000)
  centralHi := (22497855276655799423/12500000000000000000)
  directionLo := (186777022321808360373/100000000000000000000)
  directionHi := (93388511160904180187/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree015.table
  base := (1441970080183482031409788018223421349053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-164866414678539359630995325960287919750000000000)
      constant := (758496086415360205027972837710891427530554849785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree015.table
  base := (450323918103257071509402749670203441671/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-41227349755778947623746891087583034625000000000)
      constant := (189693080141135967224259729559628327376584509596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186777022321808360373/100000000000000000000)
  centralHi := (93388511160904180187/50000000000000000000)
  directionLo := (96666292785598549103/50000000000000000000)
  directionHi := (193332585571197098207/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree016.table
  base := (2742277315948089065570494440048542288443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-87903624279904012531757879101918140500000000000)
      constant := (412039226224137939696902136129699942507999626867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree016.table
  base := (2740319567576943922436759650174204788297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-263779647791034326977661218729825171500000000000)
      constant := (1236618588311461989133248196350413716728684226579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96666292785598549103/50000000000000000000)
  centralHi := (193332585571197098207/100000000000000000000)
  directionLo := (19967303578572445369/10000000000000000000)
  directionHi := (199673035785724453691/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree017.table
  base := (399117947836813233940590069120114987627/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-280122123661615035744054285671076963375000000000)
      constant := (1348089646626550725581641317714489261390812184445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree017.table
  base := (1993952119468419997657560764354506851159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-93398399015798322737613696978050711750000000000)
      constant := (449559760069400920114129774410209269314694285871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19967303578572445369/10000000000000000000)
  centralHi := (199673035785724453691/100000000000000000000)
  directionLo := (41163650856613847339/20000000000000000000)
  directionHi := (25727281785383654587/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree018.table
  base := (1343524783606683976074802782524418035473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-98844458161172677964278311345466501750000000000)
      constant := (490917865914059054178729203719509876649570674937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree018.table
  base := (1342158782865272218474249672695038935049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-98870248767918536482673654379493033000000000000)
      constant := (491144812692491315184365291041324861719373863281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41163650856613847339/20000000000000000000)
  centralHi := (25727281785383654587/12500000000000000000)
  directionLo := (52946309109071225519/25000000000000000000)
  directionHi := (211785236436284902077/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree019.table
  base := (1538848252735035690169579322605647899897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-208629750203614021361077054934481364750000000000)
      constant := (1072934585345948244741860931545765912406099102593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree019.table
  base := (153657551020755335234962129162176312961/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-313026295560116250683200835342806062750000000000)
      constant := (1610176684899656602615259700854207870911744756135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52946309109071225519/25000000000000000000)
  centralHi := (211785236436284902077/100000000000000000000)
  directionLo := (108794323092494178153/50000000000000000000)
  directionHi := (217588646184988356307/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree020.table
  base := (520462488232690492922965778490732579743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-658711752254648060380792461534089178000000000000)
      constant := (3514959679450423095325399126406629340413900569701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree020.table
  base := (518576581843198260665554280435225024859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-219627896544317927945587138364755351000000000000)
      constant := (1172234412266185949994736407623714574905032641171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108794323092494178153/50000000000000000000)
  centralHi := (217588646184988356307/100000000000000000000)
  directionLo := (22324124064531400529/10000000000000000000)
  directionHi := (223241240645314005291/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree021.table
  base := (-388624204541262424386223923577888525629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-230511417966151352226117919421578087250000000000)
      constant := (1277701138441425703461044906481281827352995028699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree021.table
  base := (-78037086726485910131248698864307948297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-230571596048558355435707053167639993500000000000)
      constant := (1278349120924615156138103989890700099951606089035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22324124064531400529/10000000000000000000)
  centralHi := (223241240645314005291/100000000000000000000)
  directionLo := (7148568755700848043/3125000000000000000)
  directionHi := (228754200182427137377/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree022.table
  base := (-602277471837480322108771402680821655691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-120726125923710008829319175832563224250000000000)
      constant := (695424865969743637368358909065189778687180628221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree022.table
  base := (-1205844575551684377380662743616241426803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-724545886658396348777480903911573908000000000000)
      constant := (4174700365554379708533107131909786674880005170879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7148568755700848043/3125000000000000000)
  centralHi := (228754200182427137377/100000000000000000000)
  directionLo := (117068694232643700467/50000000000000000000)
  directionHi := (46827477693057480187/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree023.table
  base := (-48501077329312416122765678112391618319/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-189294814296516512318369087931506107312500000000)
      constant := (1133189237696101959562925266207146460413755797670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree023.table
  base := (-1941106231944045681638242428687382328753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-252458995057039210415946882773409278500000000000)
      constant := (1511707504605012183947734038109179308088493960743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117068694232643700467/50000000000000000000)
  centralHi := (46827477693057480187/20000000000000000000)
  directionLo := (47879911968836303431/20000000000000000000)
  directionHi := (59849889961045379289/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree024.table
  base := (-2605106377972044913736255755687653141427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-263333919609957348523679216152223171000000000000)
      constant := (1637767040729251652211349939291238134304012778837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree024.table
  base := (-1302990586691771721655851393047353332023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-131701347280639818953033398788146960500000000000)
      constant := (819314757491061753960996526789522696315841208113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47879911968836303431/20000000000000000000)
  centralHi := (59849889961045379289/25000000000000000000)
  directionLo := (244548526533755253891/100000000000000000000)
  directionHi := (61137131633438813473/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree025.table
  base := (-3207641039328339089396267459665095913909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-274274753491226013956199648395771532250000000000)
      constant := (1771282091232202592745063593712856334434401609379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree025.table
  base := (-802089905573604295512170947575845518879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-205759795549140049047140034284383922625000000000)
      constant := (1329165819574864290104342515917458515115279508347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244548526533755253891/100000000000000000000)
  centralHi := (61137131633438813473/25000000000000000000)
  directionLo := (249591294732155567113/100000000000000000000)
  directionHi := (124795647366077783557/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree026.table
  base := (-469234043205286399272371448570332200703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-213911690529371009541540060479489920125000000000)
      constant := (1433531988188271120271480318292906890059859107158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree026.table
  base := (-3754461673626526857756251100318645317943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-285290093569760492886306627182063206000000000000)
      constant := (1912394160362412757040507667016266666321868387633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249591294732155567113/100000000000000000000)
  centralHi := (124795647366077783557/50000000000000000000)
  directionLo := (254534176452429855697/100000000000000000000)
  directionHi := (127267088226214927849/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree027.table
  base := (-4248708787990352879000428356538004817267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-296156421253763344821240512882868254750000000000)
      constant := (2057979214722550807764780013877647939528747661877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree027.table
  base := (-4249191399196457149681582719951680081389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-296233793074000920376426541984947848500000000000)
      constant := (2059079275284193642565195157650962325994848005259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254534176452429855697/100000000000000000000)
  centralHi := (127267088226214927849/50000000000000000000)
  directionLo := (129691441080897515731/50000000000000000000)
  directionHi := (259382882161795031463/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree028.table
  base := (-4696020888338134608196064736324930530371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-307097255135032010253760945126416616000000000000)
      constant := (2211036975401619278590324243553103692151687007301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree028.table
  base := (-2348207783421407697552326397391492781819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-460766238867362021799819685181748736500000000000)
      constant := (3318332525168624898138992088365471791141488497767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129691441080897515731/50000000000000000000)
  centralHi := (259382882161795031463/100000000000000000000)
  directionLo := (264142598107163693863/100000000000000000000)
  directionHi := (33017824763395461733/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree029.table
  base := (-203954433077998728901266689312371154143/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-954114267048902027058844132109894931750000000000)
      constant := (7111518140699616507903845461269420698987942737475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree029.table
  base := (-2549591591707442457706909973868074561671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-159060596041240887678333185795358566750000000000)
      constant := (1185889105197406808131582949030558999767762717601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264142598107163693863/100000000000000000000)
  centralHi := (33017824763395461733/12500000000000000000)
  directionLo := (53763610262349587463/20000000000000000000)
  directionHi := (67204512827936984329/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree030.table
  base := (-1364908881958557825980729931788381587459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-82244730724392335279700452403378334625000000000)
      constant := (634088086691645173980478829244980244367904779429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree030.table
  base := (-1091979700422719682831163898647887303357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-329064891586722202846786286393601776000000000000)
      constant := (2537714811499740697036860003652800360832553063335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53763610262349587463/20000000000000000000)
  centralHi := (67204512827936984329/25000000000000000000)
  directionLo := (273413564563443883307/100000000000000000000)
  directionHi := (68353391140860970827/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree031.table
  base := (-5780243101802535529516366518772454106563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-339919756778838006551322241857061699750000000000)
      constant := (2708548997431871709941456228177746024282886410853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree031.table
  base := (-2890228697346183700650401334691793183019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-510012886636443945505359301794729627750000000000)
      constant := (4065006961344150811659031773797656272643084089367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273413564563443883307/100000000000000000000)
  centralHi := (68353391140860970827/25000000000000000000)
  directionLo := (138966551608230034821/50000000000000000000)
  directionHi := (277933103216460069643/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree032.table
  base := (-6062180421898128698865277582000003513213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-1052581771980320015951528022301830183000000000000)
      constant := (8661224408761443834628056380032263302756930561009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree032.table
  base := (-30311774318063289635659627665392365151/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-87738072648800764456756528999842765250000000000)
      constant := (722156632274095843302719361769703005907606474050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138966551608230034821/50000000000000000000)
  centralHi := (277933103216460069643/100000000000000000000)
  directionLo := (56476063049675973887/20000000000000000000)
  directionHi := (70595078812094967359/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree033.table
  base := (-1576656986788698854840023137321620055693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-90450356135343834354090776586039605562500000000)
      constant := (767978261933248358493838934574787998807988332883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree033.table
  base := (-1576692452507769614918117889230698293699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-90473997524860871329286507700563925875000000000)
      constant := (768390945665244330494347001846754868118523024869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56476063049675973887/20000000000000000000)
  centralHi := (70595078812094967359/25000000000000000000)
  directionLo := (286758565723880943143/100000000000000000000)
  directionHi := (35844820715485117893/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree034.table
  base := (-1628629152634426522135288836382084971529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-93185564605661000712220884646926695875000000000)
      constant := (815762637425323423324124652187070396926101671599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree034.table
  base := (-6514631873103551752305816020297964062947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-1118519068811051738421797836815421038000000000000)
      constant := (9794409713226976511600096843129790333163231525871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286758565723880943143/100000000000000000000)
  centralHi := (35844820715485117893/12500000000000000000)
  directionLo := (58214193318214174629/20000000000000000000)
  directionHi := (145535483295535436573/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree035.table
  base := (-6686580565460857052680533482380685075553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-1151049276911738004844211912493765434250000000000)
      constant := (10381430739266903822832557226241092468600362754629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree035.table
  base := (-1337334826893169260619447719619707152573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-383783389107924340297385860408024988500000000000)
      constant := (3462334513780574640501329734818772053226537675815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58214193318214174629/20000000000000000000)
  centralHi := (145535483295535436573/50000000000000000000)
  directionLo := (29532040256051264953/10000000000000000000)
  directionHi := (295320402560512649531/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree036.table
  base := (-682339878156199391474579382906294031983/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-197311963092590666856962201537401753000000000000)
      constant := (1832091969794049915200694744954225875654646574365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree036.table
  base := (-1705868669487255229664626427215637079529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-98681772153041191946876443802727407750000000000)
      constant := (916537356252745192932679859709630479761202919599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29532040256051264953/10000000000000000000)
  centralHi := (295320402560512649531/100000000000000000000)
  directionLo := (37438694209823335067/12500000000000000000)
  directionHi := (299509553678586680537/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree037.table
  base := (-692542784746137713633547935941664512159/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-202782380033224999573222417659175933625000000000)
      constant := (1937082581913331498353928236784592797227161275645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree037.table
  base := (-277019574464190456782893319868780250283/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-1217012364349215585832877070041382820500000000000)
      constant := (11628724549219476046801539383308086199503531662975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37438694209823335067/12500000000000000000)
  centralHi := (299509553678586680537/100000000000000000000)
  directionLo := (75910228774268765403/25000000000000000000)
  directionHi := (303640915097075061613/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree038.table
  base := (-3496513919742062557343612979582830607063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-624758390921577996868447901342850342750000000000)
      constant := (6135623230594561296620538953640376674238720979059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree038.table
  base := (-3496538830189311970810733918926121202383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-208307243810322811383872802408339458000000000000)
      constant := (2046302848870564015714520075740118503947273517273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75910228774268765403/25000000000000000000)
  centralHi := (303640915097075061613/100000000000000000000)
  directionLo := (76929203613302835217/25000000000000000000)
  directionHi := (307716814453211340869/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree039.table
  base := (-7026482722200944933987622963734949578819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-427446427828987330011485699805448589750000000000)
      constant := (4312930888310922208757318643958433182109006639589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree039.table
  base := (-1405304608935652717515609203866300632509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-427558187124886050257865519619563558500000000000)
      constant := (4315237955026009924067334698735276959225578329895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76929203613302835217/25000000000000000000)
  centralHi := (307716814453211340869/100000000000000000000)
  directionLo := (311739427203995237373/100000000000000000000)
  directionHi := (155869713601997618687/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree040.table
  base := (-3513008218354522249901170001530042216481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-219193630855127997722003066024498475500000000000)
      constant := (2270854098263262260183894287802838301137494454711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree040.table
  base := (-7026049050198659962640537205108206559947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-1315505659887379433243956303267344603000000000000)
      constant := (13632405368873757749562699481654691140472725546871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311739427203995237373/100000000000000000000)
  centralHi := (155869713601997618687/50000000000000000000)
  directionLo := (315710790201598899603/100000000000000000000)
  directionHi := (78927697550399724901/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree041.table
  base := (-1747951397049898090541517734798078665641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-336996071693643495657394923219408984187500000000)
      constant := (3582558683212870931451844657314054754327608715013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree041.table
  base := (-873978993755698279950154200204746962787/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-112361396533341726309526337306333210875000000000)
      constant := (1194823676369972026446832619347075689129711237994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315710790201598899603/100000000000000000000)
  centralHi := (78927697550399724901/25000000000000000000)
  directionLo := (19977050859396387489/6250000000000000000)
  directionHi := (12785312550013687993/4000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree042.table
  base := (-6923989451659323575295554491432922340027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-460268929472793326309046996536093673500000000000)
      constant := (5018039059425482732335398363503472676532592215437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree042.table
  base := (-3462005373778141091890831170877293713957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-230194642818803666364112632014108743000000000000)
      constant := (2510357367140584806398076742853241179685231221267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19977050859396387489/6250000000000000000)
  centralHi := (12785312550013687993/4000000000000000000)
  directionLo := (64701458469559678247/20000000000000000000)
  directionHi := (80876823086949597809/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree043.table
  base := (-1364535572519461289238072092718748417167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-471209763354061991741567428779642034750000000000)
      constant := (5265589086662118383306947245510603192136226393885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree043.table
  base := (-3411347528157420228409214582523886024349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-706999477712771640327517768246653192750000000000)
      constant := (7902590485822332484620402047470712925247315135057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64701458469559678247/20000000000000000000)
  centralHi := (80876823086949597809/25000000000000000000)
  directionLo := (81833978570352595559/25000000000000000000)
  directionHi := (327335914281410382237/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree044.table
  base := (-3343978719928095224768656028947268372517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-723225895852995985761131791534785594000000000000)
      constant := (8279090649184426540821669325735367303332912973881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree044.table
  base := (-6687971314079971914352998407701613811009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-482276684646088187708465093633986771000000000000)
      constant := (5522330250307772909701656376802442080863378499479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81833978570352595559/25000000000000000000)
  centralHi := (327335914281410382237/100000000000000000000)
  directionLo := (66224054045245461801/20000000000000000000)
  directionHi := (165560135113113654503/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree045.table
  base := (-325994824653372732290878196835820877891/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-123272857779149830651652073316684689312500000000)
      constant := (1444863032633013648210380226776985807305191007105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree045.table
  base := (-203747115090328701803885653037626563963/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-123305096037582153799646252109217853375000000000)
      constant := (1445630887093458496693269341992270928345969382024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66224054045245461801/20000000000000000000)
  centralHi := (165560135113113654503/50000000000000000000)
  directionLo := (66972372193594201587/20000000000000000000)
  directionHi := (5232216577624546999/1562500000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree046.table
  base := (-6318548892786490107600897465501614442373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-504032264997867988039128725510287118500000000000)
      constant := (6045763417073260618739491946935985537754407558963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree046.table
  base := (-789819739141634854431484200683046327337/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-378123062740926782016528692429817042000000000000)
      constant := (4536729592723885125510230670782522287951722560282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66972372193594201587/20000000000000000000)
  centralHi := (5232216577624546999/1562500000000000000)
  directionLo := (169281052178895449407/50000000000000000000)
  directionHi := (67712420871558179763/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree047.table
  base := (-6083957122572723131622555105766928673689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-1544919296637409960414947473261506439250000000000)
      constant := (18954981072516563721010632465389953676288541219677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree047.table
  base := (-38024777441395410295087828694352736419/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-128776945789702367544706209510660174625000000000)
      constant := (1580419343972874793543342668144058474150592707560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169281052178895449407/50000000000000000000)
  centralHi := (67712420871558179763/20000000000000000000)
  directionLo := (342222341590111040797/100000000000000000000)
  directionHi := (171111170795055520399/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree048.table
  base := (-1163230937186464038146287934508769538247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-525913932760405318904169589997383841000000000000)
      constant := (6597142477413527047836003156364518689781852581285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree048.table
  base := (-1454040134859372323997492498274404446177/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-131512870665762474417236188211381335250000000000)
      constant := (1650159207965555091758181163603230514167782276087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342222341590111040797/100000000000000000000)
  centralHi := (171111170795055520399/50000000000000000000)
  directionLo := (345843842882393375283/100000000000000000000)
  directionHi := (86460960720598343821/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree049.table
  base := (-2757584002245130470161170208089684600099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-268427383320836992168345011120466101125000000000)
      constant := (3441104701331301537347458486567645567331681993269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree049.table
  base := (-2757586358355015895759480408080016561759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-805492773250935487738597001472614975250000000000)
      constant := (10328776177483801935460201315409056922059955868187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345843842882393375283/100000000000000000000)
  centralHi := (86460960720598343821/25000000000000000000)
  directionLo := (349427812625017793959/100000000000000000000)
  directionHi := (8735695315625444849/2500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree050.table
  base := (-2590508957466912937317507309963964028289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-821693400784413974653815681726720845250000000000)
      constant := (10760291257302604043447170673688657338770395937477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree050.table
  base := (-5181021706810026880235500346804573668653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-547938881671530752649184582451294626000000000000)
      constant := (7177318940962262451762484022672122348753923517643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349427812625017793959/100000000000000000000)
  centralHi := (8735695315625444849/2500000000000000000)
  directionLo := (176487697030237418397/50000000000000000000)
  directionHi := (70595078812094967359/20000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree051.table
  base := (-60171510619221190077772076128646095137/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-139684108601052828800432721682007231187500000000)
      constant := (1867774137836784846103724260274136507855665661940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree051.table
  base := (-4813723899602102027528422341471073228463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-558882581175771180139304497254179268500000000000)
      constant := (7475041067698150839367826554907082373754838309753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176487697030237418397/50000000000000000000)
  centralHi := (70595078812094967359/20000000000000000000)
  directionLo := (356487673543406609309/100000000000000000000)
  directionHi := (35648767354340660931/10000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree052.table
  base := (-2206644883576994707650486774365480872127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-284838634142739990317125659485788643000000000000)
      constant := (3887458179299638534518506674722866290021914290537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree052.table
  base := (-275830763724086335102233281369369572627/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-427369710510008705722068309042797933250000000000)
      constant := (5834262736637830961336250480513376770387726872444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356487673543406609309/100000000000000000000)
  centralHi := (35648767354340660931/10000000000000000000)
  directionLo := (179982842213246395383/50000000000000000000)
  directionHi := (359965684426492790767/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree053.table
  base := (-198986744370651696297849690935416086417/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 37807500000000000000000000000000000000000000
      center := (514182)
      previous := (257091)
      next := (257091)
      square := (2763974458801441216708461005107500000000000)
      linear := (-155024413180869165023167964902578937500000000)
      constant := (2158682836039459742960421380730722151297453545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree053.table
  base := (-994934214645759327086929328574790101213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (171394)
      previous := (85697)
      next := (85697)
      square := (921324819600480405569487001702500000000000)
      linear := (-51688321483112498675644742511565375000000000)
      constant := (719940062308757141272577061659103303412285267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179982842213246395383/50000000000000000000)
  centralHi := (359965684426492790767/100000000000000000000)
  directionLo := (363410410611578853781/100000000000000000000)
  directionHi := (181705205305789426891/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree054.table
  base := (-1756532134865712913218837453914124656891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-295779468024008655749646091729337004250000000000)
      constant := (4200653853582988396516327092487874818261981425421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree054.table
  base := (-878266463379503544500467040219298086361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-147928419922123115652416060415708299000000000000)
      constant := (2101432406911556395156721225562522605379501644991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363410410611578853781/100000000000000000000)
  centralHi := (181705205305789426891/50000000000000000000)
  directionLo := (91705697450158220209/25000000000000000000)
  directionHi := (366822789800632880837/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree055.table
  base := (-3013284269931453408030523012238355668703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-602499769929285976931812615702222369750000000000)
      constant := (8723879044358320040060328955156590074550620009193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree055.table
  base := (-3013285542028604631777171049678411291351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-1807972137578198670299352469397153515500000000000)
      constant := (26185398465230509062077620715721950937482634805043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91705697450158220209/25000000000000000000)
  centralHi := (366822789800632880837/100000000000000000000)
  directionLo := (18510185823848598263/5000000000000000000)
  directionHi := (370203716476971965261/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree056.table
  base := (-1240199950170961718384920149335427725977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-920160905715831963546499571918656096500000000000)
      constant := (13579051083772094966513100015041987511138639969661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree056.table
  base := (-9921603687009590878622466885585597239/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-306800539348486658794952035634301240500000000000)
      constant := (4528728025812817348917673718964354045391228326125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18510185823848598263/5000000000000000000)
  centralHi := (370203716476971965261/100000000000000000000)
  directionLo := (186777022321808360373/50000000000000000000)
  directionHi := (373554044643616720747/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree057.table
  base := (-1914415113782136966353846089012854774673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-624381437691823307796853480189319092250000000000)
      constant := (9387772685662617276495622488992967613694735900263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree057.table
  base := (-239301991705769110417339586276762124231/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-156136194550303436270005996517871780875000000000)
      constant := (2348174815372001719167116862429496855166492589922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186777022321808360373/50000000000000000000)
  centralHi := (373554044643616720747/100000000000000000000)
  directionLo := (37687459034252779397/10000000000000000000)
  directionHi := (376874590342527793971/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree058.table
  base := (-1315333027518311820016815049449122440591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-635322271573091973229373912432867453500000000000)
      constant := (9729094889660965474153186936185922981870788980121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree058.table
  base := (-328833421350702551789115351146297202623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-476616358279090629427607925655778824500000000000)
      constant := (7300646805493871744118185018067498756066143230139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37687459034252779397/10000000000000000000)
  centralHi := (376874590342527793971/100000000000000000000)
  directionLo := (380166133975780506849/100000000000000000000)
  directionHi := (7603322679515610137/2000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree059.table
  base := (-85394512485106860347213642849698499207/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-484697329090770478996420758507311861062500000000)
      constant := (7557500474774550413488095961506588135036141959102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree059.table
  base := (-170789156907750026518785865249583329641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-161608044302423650015065953919314102125000000000)
      constant := (2520486363609017171192055582143753160318013230671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380166133975780506849/100000000000000000000)
  centralHi := (7603322679515610137/2000000000000000000)
  directionLo := (23964338902961465971/6250000000000000000)
  directionHi := (383429422447383455537/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree060.table
  base := (-8943134774430285558697589275204603681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-328601969667814652047207388459982088000000000000)
      constant := (5215244944162949447142060033586325724989799017911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree060.table
  base := (-8943346392278880090629022201832955699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-328687938356967513775191865240070525500000000000)
      constant := (5217974187728426531826112078368225073237532646869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23964338902961465971/6250000000000000000)
  centralHi := (383429422447383455537/100000000000000000000)
  directionLo := (386665171142394196413/100000000000000000000)
  directionHi := (193332585571197098207/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree061.table
  base := (68047493460689833238960125172953759917/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-334072386608448984763467604581756268625000000000)
      constant := (5395281316945695990645653877103084744430081979865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree061.table
  base := (68047459528212662877841270972829842319/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-1002479364327263182560755467924538540250000000000)
      constant := (16194306723214219648241360467494801205429080878665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386665171142394196413/100000000000000000000)
  centralHi := (193332585571197098207/50000000000000000000)
  directionLo := (9746851643954701371/2500000000000000000)
  directionHi := (389874065758188054841/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree062.table
  base := (70596315344962376878194683153373250627/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-509314205323624976219591731055295673875000000000)
      constant := (8367664139492359247443221892624334509632802639445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree062.table
  base := (176490754365286293750148665015543456557/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-169815818930603970632655890021477584000000000000)
      constant := (2790678439369606888001601681561900898787132556266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9746851643954701371/2500000000000000000)
  centralHi := (389874065758188054841/100000000000000000000)
  directionLo := (98264191000289779207/25000000000000000000)
  directionHi := (393056764001159116829/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree063.table
  base := (2176466896510361058453525690463837005109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-690026440979435300391976073650609259750000000000)
      constant := (11529458531157418836009413047042461906857359803421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree063.table
  base := (435293335714201191923781807578956879913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-690206975226656310020743474888794978500000000000)
      constant := (11535476188046016912110812202245875843847653926485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98264191000289779207/25000000000000000000)
  centralHi := (393056764001159116829/100000000000000000000)
  directionLo := (198106948580372770397/50000000000000000000)
  directionHi := (79242779432149108159/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree064.table
  base := (743523988404395157202407153532827592367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-175241818715175991456124126473539405250000000000)
      constant := (2977070414694148984616832086926303686755779830023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree064.table
  base := (2974095779023394873115158627695473529151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-2103452024192690212532590169075038863000000000000)
      constant := (35743475289795101462278670634915123469123413759557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198106948580372770397/50000000000000000000)
  centralHi := (79242779432149108159/20000000000000000000)
  directionLo := (399346071571448907381/100000000000000000000)
  directionHi := (199673035785724453691/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree065.table
  base := (3804812886907012900592657961548873440631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-2135724326225917893771050814413117946750000000000)
      constant := (36880064681422716926325477971220373456341526779917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree065.table
  base := (1902406373535690257679545156152116118349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-356047187117568582500491652247282131750000000000)
      constant := (6149880237396096168741923376393179536834070840981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399346071571448907381/100000000000000000000)
  centralHi := (199673035785724453691/50000000000000000000)
  directionLo := (80490773994487527999/20000000000000000000)
  directionHi := (100613467493109409999/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree066.table
  base := (466861723006779481188657935461692912533/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-361424471311620648344768685190627171750000000000)
      constant := (6342339114823653659720158732271745464228472490385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree066.table
  base := (145894284940544463254719387101849532899/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-180759518434844398122775804824362226500000000000)
      constant := (3172820579012107393659665948172025846256117199448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80490773994487527999/20000000000000000000)
  centralHi := (100613467493109409999/25000000000000000000)
  directionLo := (405537852773368978139/100000000000000000000)
  directionHi := (20276892638668448907/5000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree067.table
  base := (5565508615368723535386387372100512186133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-733789776504509962122057802624802704750000000000)
      constant := (13082251661088664991854886078804710779581265236477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree067.table
  base := (2782754262865720725952191191286711283143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-1100972659865427029971834701150500322750000000000)
      constant := (19633585922768824916937905211998289038092410193501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405537852773368978139/100000000000000000000)
  centralHi := (20276892638668448907/5000000000000000000)
  directionLo := (408598559234216638333/100000000000000000000)
  directionHi := (204299279617108319167/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree068.table
  base := (6495486752820203938651671406025145299039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-2234191831157335882663734704605053198000000000000)
      constant := (40458225552076030952105794709656418076676843332773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree068.table
  base := (1299097336215508574811802914929736147583/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-744925472747858447471343048903218191000000000000)
      constant := (13493085368093738771729888258045144287875921107635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408598559234216638333/100000000000000000000)
  centralHi := (204299279617108319167/50000000000000000000)
  directionLo := (41163650856613847339/10000000000000000000)
  directionHi := (411636508566138473391/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree069.table
  base := (1491710282748181381498221325655738224963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-755671444267047292987098667111899427250000000000)
      constant := (13896148795219177028579884479885812850715242993735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree069.table
  base := (7458551356332915594487097712197998825493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-755869172252098874961462963706102833500000000000)
      constant := (13903366571566269746492205376627281340862032388317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41163650856613847339/10000000000000000000)
  centralHi := (411636508566138473391/100000000000000000000)
  directionLo := (414652200959748364719/100000000000000000000)
  directionHi := (5183152511996854559/1250000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree070.table
  base := (8454702417798084309040957906107332461551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-766612278148315958419619099355447788500000000000)
      constant := (14312472492116622935692959865354699768075998162119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree070.table
  base := (8454702371870247297388973115026406471119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-2300438615269017907354748635526962428000000000000)
      constant := (42959702669159769308514150880074178353406215977333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414652200959748364719/100000000000000000000)
  centralHi := (5183152511996854559/1250000000000000000)
  directionLo := (417646118546559094643/100000000000000000000)
  directionHi := (104411529636639773661/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree071.table
  base := (474196981139364466601119755980881194217/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21067500000000000000000000000000000000000000
      center := (286518)
      previous := (143259)
      next := (143259)
      square := (1540171445104790394313443158767500000000000)
      linear := (-115684355092677736141460949950257312500000000)
      constant := (2192280242913713901900704977039102161540208295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree071.table
  base := (4741969793025681580209576411880979654367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (191012)
      previous := (95506)
      next := (95506)
      square := (1026780963403193596208962105845000000000000)
      linear := (-77143083838581603842660463530239250000000000)
      constant := (1462278151214945283518296560438931437474116903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417646118546559094643/100000000000000000000)
  centralHi := (104411529636639773661/25000000000000000000)
  directionLo := (210309363149414630659/50000000000000000000)
  directionHi := (420618726298829261319/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree072.table
  base := (2109252583314490884089281807499382314427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-788493945910853289284659963842544511000000000000)
      constant := (15163870135393569671838598707980222261839487290815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree072.table
  base := (10546262887194616281268674506108252494847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-788700270764820157431822708114756761000000000000)
      constant := (15171728862472304488937430866749071994621705149143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210309363149414630659/50000000000000000000)
  centralHi := (420618726298829261319/100000000000000000000)
  directionLo := (423570472872569804153/100000000000000000000)
  directionHi := (211785236436284902077/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree073.table
  base := (582083610536483807758798279536575420491/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-199858694948030488679295099021523218062500000000)
      constant := (3899736019733276854307070648925729773858633739895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree073.table
  base := (2328334437448131314387194937510336617269/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-2398931910807181754765827868752924210500000000000)
      constant := (46821067542727998735239034346518046100055010376915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423570472872569804153/100000000000000000000)
  centralHi := (211785236436284902077/50000000000000000000)
  directionLo := (426501791398037790529/100000000000000000000)
  directionHi := (42650179139803779053/10000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree074.table
  base := (12770167435534581716031904895013748677071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-2431126841020171860449102484988923700500000000000)
      constant := (48120804307006040118774739603801276503866305354997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree074.table
  base := (31925418541893712593023590108311455227/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-202646917443325253103015634430131511500000000000)
      constant := (4012142318719248694269545244133524697533775336300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426501791398037790529/100000000000000000000)
  centralHi := (42650179139803779053/10000000000000000000)
  directionLo := (4294131002216610207/1000000000000000000)
  directionHi := (429413100221661020701/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree075.table
  base := (6965874268004636836089699578764356875557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-410658223777329642791110630286594797375000000000)
      constant := (8243921102410895610021601776020292622991230339133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree075.table
  base := (6965874260500812074803074567259688839051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-410765684638770719951091226261705344250000000000)
      constant := (8248184571800056595748039653783347936239000959619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4294131002216610207/1000000000000000000)
  centralHi := (429413100221661020701/100000000000000000000)
  directionLo := (432304803602991719103/100000000000000000000)
  directionHi := (6754762556296745611/1562500000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree076.table
  base := (472700483400152548271460402744276803231/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-208064320358981987753685423204184489000000000000)
      constant := (4235416596444653406660592404304643317875995648312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree076.table
  base := (7563207728406053063187922959161444790543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-1248712603172672801088453550989442996500000000000)
      constant := (25425633179701282335489111042483409118554775445301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432304803602991719103/100000000000000000000)
  centralHi := (6754762556296745611/1562500000000000000)
  directionLo := (435177292369976712613/100000000000000000000)
  directionHi := (217588646184988356307/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree077.table
  base := (3270833639948618199041313368080616574973/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-2529594345951589849341786375180858951750000000000)
      constant := (52205221934165529656668869677154389129129470256555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree077.table
  base := (654166727606447734173899882397168094299/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-843418768286022294882422282129179973500000000000)
      constant := (17410728202997381358278006737516020064948294413275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435177292369976712613/100000000000000000000)
  centralHi := (217588646184988356307/50000000000000000000)
  directionLo := (438030944535551211583/100000000000000000000)
  directionHi := (6844233508367987681/1562500000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree078.table
  base := (17615006701877356832918316728126655588307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-854138949198465281879782557303834678500000000000)
      constant := (17868064981269912362916807655354314041566471543883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree078.table
  base := (3523001338844595087072464567458907120133/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-854362467790262722372542196932064616000000000000)
      constant := (17877287392809833170535091825450024874256932912385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438030944535551211583/100000000000000000000)
  centralHi := (6844233508367987681/1562500000000000000)
  directionLo := (220433062939155121041/50000000000000000000)
  directionHi := (440866125878310242083/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree079.table
  base := (18908930953963949556105637131503715638631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-865079783079733947312302989547383039750000000000)
      constant := (18340639395122006258789333664924858913797520388639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree079.table
  base := (18908930947850345894842054360027136579439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-2595918501883509449587986335204847775500000000000)
      constant := (55050299066816291176668920402726692436246564495573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220433062939155121041/50000000000000000000)
  centralHi := (440866125878310242083/100000000000000000000)
  directionLo := (221841595244891485169/50000000000000000000)
  directionHi := (443683190489782970339/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree080.table
  base := (316186577175878203088981515440359927777/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-657015462720751959558617566343198550750000000000)
      constant := (14114597914530741983786394952747276054161205487024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree080.table
  base := (404718818687480256529901094085546806943/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-438124933399371788676391013268916950500000000000)
      constant := (9414582545574066516419114960882143246093081334175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221841595244891485169/50000000000000000000)
  centralHi := (443683190489782970339/100000000000000000000)
  directionLo := (22324124064531400529/5000000000000000000)
  directionHi := (446482481290628010581/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree081.table
  base := (2699504580569207295336092889486112098809/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-221740362710567819544335963508619940562500000000)
      constant := (4826134613459985177329669248598922386282050902442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree081.table
  base := (10798018320327727032843697565286611483823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-443596783151492002421450970670359271750000000000)
      constant := (9657241799625948699059699466965656250438899446087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22324124064531400529/5000000000000000000)
  centralHi := (446482481290628010581/100000000000000000000)
  directionLo := (112316082629470005201/25000000000000000000)
  directionHi := (89852866103576004161/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree082.table
  base := (4597843611890436998673383751574391088813/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-897902284723539943609864286278028123500000000000)
      constant := (19795863098371536288149395448283300724729680446985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree082.table
  base := (5747304514085030958039554497398541432417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-673602949355418324249766392107702389500000000000)
      constant := (14854541409827576027424812421757989606515830395419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112316082629470005201/25000000000000000000)
  centralHi := (89852866103576004161/20000000000000000000)
  directionLo := (452029060185207441377/100000000000000000000)
  directionHi := (226014530092603720689/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree083.table
  base := (6103871293938164685964170256208068966777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-681632338953606456781788538891182363562500000000)
      constant := (15220078364639756277247104804750014674791449990939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree083.table
  base := (24415485173268570280136700027396665220219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-909080965311464859823141770946487828500000000000)
      constant := (20303879932587205731095806014457337490835973257011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452029060185207441377/100000000000000000000)
  centralHi := (226014530092603720689/50000000000000000000)
  directionLo := (454776982517986326891/100000000000000000000)
  directionHi := (113694245629496581723/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree084.table
  base := (12937418993497310058138128833460591251919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-459891976243038637237452575382562423000000000000)
      constant := (10398631308596437877775624415734239299904594614311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree084.table
  base := (3234354748126509450924742812235820523457/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-230006166203926321828315421437343117750000000000)
      constant := (5201989439403044687793688537004696297681639168466) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454776982517986326891/100000000000000000000)
  centralHi := (113694245629496581723/25000000000000000000)
  directionLo := (457508400364854274753/100000000000000000000)
  directionHi := (228754200182427137377/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree085.table
  base := (27367276488088529147460315553704588308121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-930724786367345939907425583008673207250000000000)
      constant := (21307337491319069699804047831620432109057479932449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree085.table
  base := (1710454780406655612552402013870733725603/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-698226273239959286102536200414192835125000000000)
      constant := (15988716516079983407582272251438568329775894782884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457508400364854274753/100000000000000000000)
  centralHi := (228754200182427137377/50000000000000000000)
  directionLo := (460223607587280056271/100000000000000000000)
  directionHi := (28763975474205003517/6250000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree086.table
  base := (28892800675025763722645230648395090545607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-2824996860745843816019838045756664705500000000000)
      constant := (65470987325524482307457039286127524763032041982749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree086.table
  base := (28892800673763495930389201387158128660111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-941912063824186142293501515355141756000000000000)
      constant := (21834872724014127866145294810276478216925915318759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460223607587280056271/100000000000000000000)
  centralHi := (28763975474205003517/6250000000000000000)
  directionLo := (462922889428567455959/100000000000000000000)
  directionHi := (11573072235714186399/2500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree087.table
  base := (6090282108929985798548293329696153794241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-952606454129883270772466447495769929750000000000)
      constant := (22346237468715453879102307292559503120483781433645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree087.table
  base := (30451410543642934727103484784256385216471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-952855763328426569783621430158026398500000000000)
      constant := (22357709865290163533346346925726805808025580943599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462922889428567455959/100000000000000000000)
  centralHi := (11573072235714186399/2500000000000000000)
  directionLo := (58200815357950613611/12500000000000000000)
  directionHi := (465606522863604908889/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree088.table
  base := (16021553047238258727312807299337039126177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-481773644005575968102493439869659145500000000000)
      constant := (11437531285952883991763967462254215810986278643913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree088.table
  base := (32043106093673277852682567509109782005783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-2891398388498000991821224034882733123000000000000)
      constant := (68660400335699262858262761118231886677265138771981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58200815357950613611/12500000000000000000)
  centralHi := (465606522863604908889/100000000000000000000)
  directionLo := (468274776930574801869/100000000000000000000)
  directionHi := (46827477693057480187/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree089.table
  base := (33667887322550698835780173136240148172751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-2923464365677261804912521935948599956750000000000)
      constant := (70230413254154267066212196349405713083063273564757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree089.table
  base := (420848591523875862847013317645479697/125000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-243685790584226856190965314940948920875000000000)
      constant := (5855535865953841573710022524753223527482088360000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468274776930574801869/100000000000000000000)
  centralHi := (46827477693057480187/10000000000000000000)
  directionLo := (235463956522873443239/50000000000000000000)
  directionHi := (470927913045746886479/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree090.table
  base := (17662877113667589709877883812114184588883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-492714477886844633535013872113207506750000000000)
      constant := (11975731503565324327951568821818193530841403801227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree090.table
  base := (35325754226824304784551634139896537044779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-985686861841147852253981174566680326000000000000)
      constant := (23963739921015348612098401252448855868943831207651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235463956522873443239/50000000000000000000)
  centralHi := (470927913045746886479/100000000000000000000)
  directionLo := (118391546325599587351/25000000000000000000)
  directionHi := (94713237060479669881/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree091.table
  base := (7403341361524354852573995218516841921281/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-996369789654957932502548176469963374750000000000)
      constant := (24499038339126338782039352928586594616422180782445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree091.table
  base := (9254176701803606019138036486968227491881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-747472921009041209808075817027173726375000000000)
      constant := (18383692112612015197785175133981553220582380763667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118391546325599587351/25000000000000000000)
  centralHi := (94713237060479669881/20000000000000000000)
  directionLo := (47618984075482799021/10000000000000000000)
  directionHi := (476189840754827990211/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree092.table
  base := (9685186265615419854294203013274054812569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-755482967652169948451301456535133802000000000000)
      constant := (18789647810518793132171446699830802286914971092483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree092.table
  base := (7748149012427382908678317188789557309229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1007574260849628707234221004172449611000000000000)
      constant := (25065692151204020955209144404025687636669339498505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47618984075482799021/10000000000000000000)
  centralHi := (476189840754827990211/100000000000000000000)
  directionLo := (478799119688363034311/100000000000000000000)
  directionHi := (59849889961045379289/12500000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree093.table
  base := (809957379822209818347051450706556074023/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-509125728708747631683794520478530048625000000000)
      constant := (12806469615908131976258805941716314089735585997175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree093.table
  base := (10124467247712899694001323087300473916737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-254629490088467283681085229743833563375000000000)
      constant := (6406511981042217412345699046470592095073900348553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478799119688363034311/100000000000000000000)
  centralHi := (59849889961045379289/12500000000000000000)
  directionLo := (481394255876193790847/100000000000000000000)
  directionHi := (3760892624032763991/781250000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree094.table
  base := (2114403929649242647276359914216500999361/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-257298072824690982200027368300152114625000000000)
      constant := (6544816198122924423484557130117794722080915760045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree094.table
  base := (5286009824097312036933269146515843260487/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-772096244893582171660845625333664172000000000000)
      constant := (19644492601776765293477160009797819793007291653818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481394255876193790847/100000000000000000000)
  centralHi := (3760892624032763991/781250000000000000)
  directionLo := (483975476823813140217/100000000000000000000)
  directionHi := (241987738411906570109/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree095.table
  base := (11027843466907069150965924036990548697819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-780099843885024445674472429083117614812500000000)
      constant := (20063880322033671080412837465052925397373962789233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree095.table
  base := (22055686933731906667648490140828450748539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-520202679681174994852290374290551769250000000000)
      constant := (13382759392899023692272466183494590469873113743091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483975476823813140217/100000000000000000000)
  centralHi := (241987738411906570109/50000000000000000000)
  directionLo := (243271502000892122537/50000000000000000000)
  directionHi := (19461720160071369803/4000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree096.table
  base := (22983877407342095218854322843330692259209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-525536979530650629832575168843852590500000000000)
      constant := (13665333071235403040147903956189263768277391246321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree096.table
  base := (2298387740727656505618698598138746503387/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-262837264716647604298675165845997045250000000000)
      constant := (6836158468612732996270744216862873838680594962015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243271502000892122537/50000000000000000000)
  centralHi := (19461720160071369803/4000000000000000000)
  directionLo := (244548526533755253891/50000000000000000000)
  directionHi := (489097053067510507783/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree097.table
  base := (23928610716937346853952605732570631941037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-531007396471284962548835384965626771125000000000)
      constant := (13957870965882748245871308345063108489522663205253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree097.table
  base := (23928610716885131714272735165891350830801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-1593439137556246267027230867280309235250000000000)
      constant := (41895003102485645088234338326781032651879172696107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244548526533755253891/50000000000000000000)
  centralHi := (489097053067510507783/100000000000000000000)
  directionLo := (491637834076636274191/100000000000000000000)
  directionHi := (30727364629789767137/6250000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree098.table
  base := (49779773724983806630779397097722875766607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-3218866880471515771590573606524405710500000000000)
      constant := (85521203391777723093960407170761096934407229029749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree098.table
  base := (49779773724900604302733398853977381816429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1073236457875071272174940492989757466000000000000)
      constant := (28521623367413502706323695052270433678573161616501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491637834076636274191/100000000000000000000)
  centralHi := (30727364629789767137/6250000000000000000)
  directionLo := (61770693960583096439/12500000000000000000)
  directionHi := (494165551684664771513/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree099.table
  base := (51735411687844266701313700824493944003813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1083896460705107255962711634418350264750000000000)
      constant := (29104643738949671233689953839882818278109591224397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree099.table
  base := (25867705843888992069072280132912563116253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-542090078689655849832530203896321054250000000000)
      constant := (14559748885858898476086150419699377157089934126757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61770693960583096439/12500000000000000000)
  centralHi := (494165551684664771513/100000000000000000000)
  directionLo := (124170101334835240877/25000000000000000000)
  directionHi := (496680405339340963509/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree100.table
  base := (53724135322327121231108673548277293187397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1094837294586375921395232066661898626000000000000)
      constant := (29708469756834961106991330500290648652271090190093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree100.table
  base := (53724135322274323069962371485965287895277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-3285371570650656381465540967786580253000000000000)
      constant := (89170875843704497491512228826413128489192329865439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124170101334835240877/25000000000000000000)
  centralHi := (496680405339340963509/100000000000000000000)
  directionLo := (499182589464311134227/100000000000000000000)
  directionHi := (124795647366077783557/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree101.table
  base := (55745944628333524757191534352013749614709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-3317334385402933760483257496716340961750000000000)
      constant := (90955637552741132948291063653874971653971080477463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree101.table
  base := (55745944628291471961950637251996657543739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1106067556387792554645300237398411393500000000000)
      constant := (30334005895963219532962712811654698756285719131891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499182589464311134227/100000000000000000000)
  centralHi := (124795647366077783557/25000000000000000000)
  directionLo := (100334458726907564711/20000000000000000000)
  directionHi := (125418073408634455889/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree102.table
  base := (11560167921157654998482691694595469952637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1116718962348913252260272931148995348500000000000)
      constant := (30934872021184855983911812106094259431100059578265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree102.table
  base := (1806276237679836999162692390974921577379/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-279252813973008245533855038050324009000000000000)
      constant := (7737659903975475261916426252100551069723215736408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100334458726907564711/20000000000000000000)
  centralHi := (125418073408634455889/25000000000000000000)
  directionLo := (126037425685979502131/25000000000000000000)
  directionHi := (20165988109756720341/4000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree103.table
  base := (11977764050926943915274672444659329015941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1127659796230181917692793363392543709750000000000)
      constant := (31557448267647593903438174911895052329813203770145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree103.table
  base := (29944410127304024877246273981052963199007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-1691932433094410114438310100506271017750000000000)
      constant := (47360289661575121661092728528304629263093034256549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126037425685979502131/25000000000000000000)
  centralHi := (20165988109756720341/4000000000000000000)
  directionLo := (101322999433104789837/20000000000000000000)
  directionHi := (253307498582761974593/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree104.table
  base := (31004943287415371816778111767913663205579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-1707900945167175874687970693454138106500000000000)
      constant := (48279411885451992581382104441276814723700241148553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree104.table
  base := (31004943287404753860511402769341953971369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-569449327450256918557829990903532660500000000000)
      constant := (16101333185703584180526381504079110196524806201361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101322999433104789837/20000000000000000000)
  centralHi := (253307498582761974593/50000000000000000000)
  directionLo := (101813670580971942279/20000000000000000000)
  directionHi := (127267088226214927849/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree105.table
  base := (64164038566345609457952744554694123932513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1149541463992719248557834227879640432250000000000)
      constant := (32821350989145624185249732279752200425417891174697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree105.table
  base := (16041009641582175468174702395741107656703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-287460588601188566151444974152487490875000000000)
      constant := (8209514851743182886632520896332142987986420962807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101813670580971942279/20000000000000000000)
  centralHi := (127267088226214927849/25000000000000000000)
  directionLo := (102301988349300374457/20000000000000000000)
  directionHi := (255754970873250936143/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree106.table
  base := (265405104916629871979720079731378436179/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (342788)
      previous := (171394)
      next := (171394)
      square := (1842649639200960811138974003405000000000000)
      linear := (-206565022761478802775072029213810750000000000)
      constant := (5956332763293017427931126859366813477722292375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree106.table
  base := (1327025524582880155069414979647378334411/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 75615000000000000000000000000000000000000000
      center := (1028364)
      previous := (514182)
      next := (514182)
      square := (5527948917602882433416922010215000000000000)
      linear := (-619857273358309732340281138169901000000000000)
      constant := (17878091250131611494059228739378043876282438825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102301988349300374457/20000000000000000000)
  centralHi := (255754970873250936143/50000000000000000000)
  directionLo := (128484982848617538533/25000000000000000000)
  directionHi := (513939931394470154133/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree107.table
  base := (68571599563251399921296257466971771925379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-3514269395265769738268625277100211464250000000000)
      constant := (102330762046214280906156970437053519825320653587153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree107.table
  base := (17142899890810171271733970028472885813243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-292932438353308779896504931553929812125000000000)
      constant := (8531901198432039592570572437058230073228535818067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128484982848617538533/25000000000000000000)
  centralHi := (513939931394470154133/100000000000000000000)
  directionLo := (103271697121330515809/20000000000000000000)
  directionHi := (258179242803326289523/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree108.table
  base := (17706252142154468548492130093951665913737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-295590991409131311213848881152571379000000000000)
      constant := (8691020160704813599968672490799590386513805341553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree108.table
  base := (70825008568609345546988609901789866002283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1182673452917475547076139641018603891000000000000)
      constant := (34781757144917680343467923462403739523079681665827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103271697121330515809/20000000000000000000)
  centralHi := (258179242803326289523/50000000000000000000)
  directionLo := (129691441080897515731/25000000000000000000)
  directionHi := (20750630572943602517/4000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree109.table
  base := (73111503245251535650322306206934241566473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1193304799517793910287915956853833877250000000000)
      constant := (35424157346423578373576384710197211468382144913937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree109.table
  base := (731115032452447477168091998016558841081/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-895212864316286980924694666866116400125000000000)
      constant := (26581621950986217118562887416097332419259770201675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129691441080897515731/25000000000000000000)
  centralHi := (20750630572943602517/4000000000000000000)
  directionLo := (521161923791907056497/100000000000000000000)
  directionHi := (260580961895953528249/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree110.table
  base := (75431083593150251942914668532183361485769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-3612736900197187727161309167292146715500000000000)
      constant := (108271452378653106086271746642200619838973490404883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree110.table
  base := (75431083593144849894573638448364746208189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1204560851925956402056379470624373176000000000000)
      constant := (36108821162919956903287193416222942799325065423941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521161923791907056497/100000000000000000000)
  centralHi := (260580961895953528249/50000000000000000000)
  directionLo := (523547116682657787631/100000000000000000000)
  directionHi := (32721694792666111727/6250000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree111.table
  base := (19445937403078591209381945013659552280031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-303796616820082810288239205335232649937500000000)
      constant := (9190765245550407551219629114367551467681214910239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree111.table
  base := (38891874806155033037476603100834915902473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-607752275715098414773249692713628909250000000000)
      constant := (18390866414866344220656232238011863448045430197937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523547116682657787631/100000000000000000000)
  centralHi := (32721694792666111727/6250000000000000000)
  directionLo := (525921492204841765789/100000000000000000000)
  directionHi := (52592149220484176579/10000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree112.table
  base := (20042375325686525633019119226557676948411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-306531825290399976646369313396119740250000000000)
      constant := (9360471978593848613399806741910667893086904041459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree112.table
  base := (16033900260548536400732141254163226704673/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-3679344752803311771109857900690427383000000000000)
      constant := (112382692805259549416115742159316340921852241546055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525921492204841765789/100000000000000000000)
  centralHi := (52592149220484176579/10000000000000000000)
  directionLo := (264142598107163693863/50000000000000000000)
  directionHi := (528285196214327387727/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree113.table
  base := (8258833866444911882390919856428496078883/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-1855602202564302858026996528742040983375000000000)
      constant := (57190447384108569769960989099204177032169652918405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree113.table
  base := (82588338664446397324006158389841343801029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1237391950438677684526739215033027103500000000000)
      constant := (38146315478981493383040051746295411810190923013901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264142598107163693863/50000000000000000000)
  centralHi := (528285196214327387727/100000000000000000000)
  directionLo := (6632979641480108151/1250000000000000000)
  directionHi := (530638371318408652081/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree114.table
  base := (42520130848714066092071779356286327207661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-624004484462068618725259059035787841750000000000)
      constant := (19409146003646326599175630390794732426790402854709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree114.table
  base := (10630032712178245878369565408870628061143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-312083912485729528004214782458977936500000000000)
      constant := (9709496615354421626448140798173752691432604426334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6632979641480108151/1250000000000000000)
  centralHi := (530638371318408652081/100000000000000000000)
  directionLo := (532981156976207075271/100000000000000000000)
  directionHi := (66622644622025884409/12500000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree115.table
  base := (4376263520084432174989430130824049723293/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-314737450701351475720759637578781011187500000000)
      constant := (9878967292009073100555182274872311188303426207585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree115.table
  base := (10940658800210865135935159731873997442629/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-944459512085368904630234283479097291375000000000)
      constant := (29651932911796380609257186466720732145420104165806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532981156976207075271/100000000000000000000)
  centralHi := (66622644622025884409/12500000000000000000)
  directionLo := (267656844797559416811/50000000000000000000)
  directionHi := (535313689595118833623/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree116.table
  base := (90043364777236715740747914248459877011939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-3809671910060023704946676947676017218000000000000)
      constant := (120659089214910149932782623047773118778249813773073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree116.table
  base := (22510841194308836410421346198366568348673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-317555762237849741749274739860420257750000000000)
      constant := (10060021935478510620851727826994465039517260605737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267656844797559416811/50000000000000000000)
  centralHi := (535313689595118833623/100000000000000000000)
  directionLo := (53763610262349587463/10000000000000000000)
  directionHi := (537636102623495874631/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree117.table
  base := (18518908964815760470855347999771282648157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1280831470567943233748079414802220767250000000000)
      constant := (40929773718094017306375463405918804435262415792665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree117.table
  base := (46297272412038856292522324439130172773261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-640583374227819697243609437122282836750000000000)
      constant := (20475259019987191581059119490504793113984199441109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53763610262349587463/10000000000000000000)
  centralHi := (537636102623495874631/100000000000000000000)
  directionLo := (539948526639739186149/100000000000000000000)
  directionHi := (10798970532794783723/2000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree118.table
  base := (4758940527111080699255201953300148616017/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-322943076112302974795149961761442282125000000000)
      constant := (10411525276852072353106989322728757536584896634365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree118.table
  base := (95178810542220747251992099548476049914599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-3876331343879639465932016367142350948000000000000)
      constant := (125001604329728874241047154572287435589854472221693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539948526639739186149/100000000000000000000)
  centralHi := (10798970532794783723/2000000000000000000)
  directionLo := (271125544718986266657/50000000000000000000)
  directionHi := (108450217887594506663/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree119.table
  base := (19559232386334403064750981915997315069389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-3908139414991441693839360837867952469250000000000)
      constant := (127106035718738890502788972277529998788236612001115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree119.table
  base := (48898080965835663014444944141854179584593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-651527073732060124733729351925167479250000000000)
      constant := (21195068975859932304446173148695600964289811676217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271125544718986266657/50000000000000000000)
  centralHi := (108450217887594506663/20000000000000000000)
  directionLo := (54454391611045572067/10000000000000000000)
  directionHi := (544543916110455720671/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree120.table
  base := (10044659899243694562363684941489431257153/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-656826986105874615022820355766432925500000000000)
      constant := (21548753057304068916440773903233963351575844694285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree120.table
  base := (100446598992436397480439400178962540729349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1313997846968360676957578618653219601000000000000)
      constant := (43119327565405201140598602348375112066396965099981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54454391611045572067/10000000000000000000)
  centralHi := (544543916110455720671/100000000000000000000)
  directionLo := (109365425825377553323/20000000000000000000)
  directionHi := (68353391140860970827/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree121.table
  base := (12891265215565419724721723346233115914019/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-331148701523254473869540285944103553062500000000)
      constant := (10958145933123477715676772389283120431847337643422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree121.table
  base := (103130121724522921931912985377953483031221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-3974824639417803313343095600368312730500000000000)
      constant := (131564310852897198704549913378329158154425914909047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109365425825377553323/20000000000000000000)
  centralHi := (68353391140860970827/12500000000000000000)
  directionLo := (549100848410742247649/100000000000000000000)
  directionHi := (10982016968214844953/2000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree122.table
  base := (6615420632996135755402027701503815330693/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-1001651729980714920683011182014971930125000000000)
      constant := (33430433569927785436633485045355415745627282705404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree122.table
  base := (105846730127937825523574873305592256333047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1335885245976841531937818448258988886000000000000)
      constant := (44596466108401557966963111823906537448642265804943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549100848410742247649/100000000000000000000)
  centralHi := (10982016968214844953/2000000000000000000)
  directionLo := (137841297853192360823/25000000000000000000)
  directionHi := (551365191412769443293/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree123.table
  base := (108596424202688241138598263404997977966287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1346476473855555226343202008263510934750000000000)
      constant := (45321489196837644025961950890957903363824962722503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree123.table
  base := (108596424202687965600283293178069420600687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1346828945481081959427938363061873528500000000000)
      constant := (45344415037712773438100108248507562123219059436103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137841297853192360823/25000000000000000000)
  centralHi := (551365191412769443293/100000000000000000000)
  directionLo := (553620273181792753741/100000000000000000000)
  directionHi := (276810136590896376871/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree124.table
  base := (55689601974390162010836625404054201978379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-678708653868411945887861220253529648000000000000)
      constant := (23037658521647898451797848404509223146861480986051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree124.table
  base := (111379203948780104966621266787793086690213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4073317934955967160754174833594274513000000000000)
      constant := (138295851216698425232150309889071925525695200177991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553620273181792753741/100000000000000000000)
  centralHi := (276810136590896376871/50000000000000000000)
  directionLo := (111173241286584027857/20000000000000000000)
  directionHi := (277933103216460069643/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree125.table
  base := (114195069366221067203014359575540108694927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4105074424854277671624728618251822971750000000000)
      constant := (140506184897834799990540735805900737345687794787989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree125.table
  base := (114195069366220893063911257162039194168399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1368716344489562814408178192667642813500000000000)
      constant := (46859072211961757042025978627418255518579594299431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111173241286584027857/20000000000000000000)
  centralHi := (277933103216460069643/50000000000000000000)
  directionLo := (22324124064531400529/4000000000000000000)
  directionHi := (279051550806642506613/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree126.table
  base := (117044020455016990964076496839038017118469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1379298975499361222640763304994156018500000000000)
      constant := (47601722964785145634002925320668115230353664061261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree126.table
  base := (117044020455016852540031016999285805090163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1379660043993803241898298107470527456000000000000)
      constant := (47625780456899711693824010711241058554752768317547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22324124064531400529/4000000000000000000)
  centralHi := (279051550806642506613/50000000000000000000)
  directionLo := (560331066965425081119/100000000000000000000)
  directionHi := (3502069168533906757/625000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree127.table
  base := (119926057215174480036679682477200400534163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1390239809380629888073283737237704379750000000000)
      constant := (48374301039816524223945328124186365643908000853547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree127.table
  base := (23985211443034874001928645661106400202573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4171811230494131008165254066820236295500000000000)
      constant := (145196225421140288404961483009071770877344768722555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560331066965425081119/100000000000000000000)
  centralHi := (3502069168533906757/625000000000000000)
  directionLo := (281275104294201016531/50000000000000000000)
  directionHi := (562550208588402033063/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree128.table
  base := (24568235929339955501996678859109134585091/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4203541929785695660517412508443758223000000000000)
      constant := (147459387573117472509615101858598660691529501605685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree128.table
  base := (61420589823349845029936040907349982104927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-700773721501142048439268968538148370500000000000)
      constant := (24588978131201499394962221633773711432752742052663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281275104294201016531/50000000000000000000)
  centralHi := (562550208588402033063/100000000000000000000)
  directionLo := (564760630496759738871/100000000000000000000)
  directionHi := (70595078812094967359/12500000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree129.table
  base := (25157877549919796252173428912294213508541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1412121477143167218938324601724801102250000000000)
      constant := (49938207418453131818749197893051597003116680017145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree129.table
  base := (3930918367174965992477062144426443994943/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-353122785626631131092164462969795345875000000000)
      constant := (12490855955742126505619311397649049882744736702936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell151.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564760630496759738871/100000000000000000000)
  centralHi := (70595078812094967359/12500000000000000000)
  directionLo := (7087030433467670583/1250000000000000000)
  directionHi := (566962434677413646641/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree130.table
  base := (16096335190484755290151476923297361480097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-355765577756108971092711258492087365875000000000)
      constant := (12682383930514632859548744405827257365569839812786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree130.table
  base := (5150827260955119483505468997802805372289/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4270304526032294855576333300046198078000000000000)
      constant := (152265433466230106341056761934851654361554011763075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7087030433467670583/1250000000000000000)
  centralHi := (566962434677413646641/100000000000000000000)
  directionLo := (569155721144559422939/100000000000000000000)
  directionHi := (28457786057227971147/5000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree131.table
  base := (8236566310596422795138724963031987704131/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-1075502358679278412352524099658923368562500000000)
      constant := (38645335576391578910703808098424942125336300372668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree131.table
  base := (26357012193908544166035220900688881730661/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1434378541515005379348897681484950668500000000000)
      constant := (51553118259727669260288793210280569992917111208545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569155721144559422939/100000000000000000000)
  centralHi := (28457786057227971147/5000000000000000000)
  directionLo := (114268117598536895841/20000000000000000000)
  directionHi := (285670293996342239603/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree132.table
  base := (134832526086598806455631120534482562521779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1444943978786973215235885898455446186000000000000)
      constant := (52330942557843933265098745255507354026736456820651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree132.table
  base := (26966505217319754315661685486517848564997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1445322241019245806839017596287835311000000000000)
      constant := (52357345135921487588897733327216192302983825022465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114268117598536895841/20000000000000000000)
  centralHi := (285670293996342239603/50000000000000000000)
  directionLo := (286758565723880943143/50000000000000000000)
  directionHi := (573517131447761886287/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree133.table
  base := (34478269218762920317549274715535789099677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-363971203167060470167101582674748636812500000000)
      constant := (13285255272506023416572528682897150927772049790413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree133.table
  base := (137913076875051653557706894585617692115301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4368797821570458702987412533272159860500000000000)
      constant := (159503475351974705545639532975825330269321638937607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286758565723880943143/50000000000000000000)
  centralHi := (573517131447761886287/100000000000000000000)
  directionLo := (575685445916702271361/100000000000000000000)
  directionHi := (287842722958351135681/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree134.table
  base := (70513356667453380541766871713791569858289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-2200238469824265819151390144413814362750000000000)
      constant := (80936024547593993727660728234851040623327909872523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree134.table
  base := (3525667833372668476631314104546852147589/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-366802410006931665454814356473401149000000000000)
      constant := (13496139550984497027966720040435519531622481825410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575685445916702271361/100000000000000000000)
  centralHi := (287842722958351135681/50000000000000000000)
  directionLo := (288922812017567801887/50000000000000000000)
  directionHi := (23113824961405424151/4000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree135.table
  base := (28834687093233855767616019415042361543469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1477766480430779211533447195186091269750000000000)
      constant := (54779928382959713820899161649318700465924671931305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree135.table
  base := (144173435466169261344967673030433800517309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1478153339531967089309377340696489238500000000000)
      constant := (54807544395760820482478613949591624475668632865221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288922812017567801887/50000000000000000000)
  centralHi := (23113824961405424151/4000000000000000000)
  directionLo := (28999887835679564731/5000000000000000000)
  directionHi := (579997756713591294621/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree136.table
  base := (73676621634422165834038129658980472340943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-744353657156023938482983813714819815500000000000)
      constant := (27804378571857659924974199352761277806547578499367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree136.table
  base := (36838310817211079442722078400043366874121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-1116822779277155637599622941624530410750000000000)
      constant := (41727587769595103355044639727712002110049665259347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28999887835679564731/5000000000000000000)
  centralHi := (579997756713591294621/100000000000000000000)
  directionLo := (58214193318214174629/10000000000000000000)
  directionHi := (582141933182141746291/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree137.table
  base := (30113227348587376854899396674995662937429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4498944444579949627195464179019563976750000000000)
      constant := (169331507941988652619779100886486056697095153482515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree137.table
  base := (150566136742936873234643904042218925853391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1500040738540447944289617170302258523500000000000)
      constant := (56472276095036010388314136470206822560363735783079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58214193318214174629/10000000000000000000)
  centralHi := (582141933182141746291/100000000000000000000)
  directionLo := (3651739006459821129/625000000000000000)
  directionHi := (584278241033571380641/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree138.table
  base := (153812115888451772428442577269996513690233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1510588982074585207831008491916736353500000000000)
      constant := (57285164893802475366169092096805199893295762929377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree138.table
  base := (76906057944225881829454278915769228673301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-755492219022344185889868542552571583000000000000)
      constant := (28657010801244253352362400414047405927951087947869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3651739006459821129/625000000000000000)
  centralHi := (584278241033571380641/100000000000000000000)
  directionLo := (586406766265130236647/100000000000000000000)
  directionHi := (73300845783141279581/12500000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree139.table
  base := (157091180705393706541977701114730423842877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1521529815955853873263528924160284714750000000000)
      constant := (58132743883134160028907469335561540206970830266213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree139.table
  base := (157091180705393699576242909933247740977433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4565784412646786397809570999724083425500000000000)
      constant := (174486060645453080373685953913399953457669779398531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586406766265130236647/100000000000000000000)
  centralHi := (73300845783141279581/12500000000000000000)
  directionLo := (147131898329732112523/25000000000000000000)
  directionHi := (588527593318928450093/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree140.table
  base := (40100832798441818814974505122414158637213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-1149352987377841904022037017302874807000000000000)
      constant := (44239929711493502378095464705138553584918487306991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree140.table
  base := (80201665596883634863613321219057958648527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-766435918526584613379988457355456225500000000000)
      constant := (29508135966511817812583896677846952410258153921063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147131898329732112523/25000000000000000000)
  centralHi := (588527593318928450093/100000000000000000000)
  directionLo := (29532040256051264953/5000000000000000000)
  directionHi := (590640805121025299061/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree141.table
  base := (20468570919197118629655706314293010222481/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-385852870929597801032142447161845359312500000000)
      constant := (14961663022593517023556861540721336238141632743578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree141.table
  base := (163748567353576944643037178631584521124983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1543815536557409654250096829513797093500000000000)
      constant := (59876776756106396510019219064482960232445079402127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29532040256051264953/5000000000000000000)
  centralHi := (590640805121025299061/100000000000000000000)
  directionLo := (5927464831192640109/1000000000000000000)
  directionHi := (592746483119264010901/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree142.table
  base := (83563444592413541838128785954683086485983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (191012)
      previous := (95506)
      next := (95506)
      square := (1026780963403193596208962105845000000000000)
      linear := (-154171029319545712116751658489479250000000000)
      constant := (6021918399948662614372520851886175555564126247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree142.table
  base := (41781722296206770046606246147197560843243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21067500000000000000000000000000000000000000
      center := (286518)
      previous := (143259)
      next := (143259)
      square := (1540171445104790394313443158767500000000000)
      linear := (-231317085309707907420186978424422000000000000)
      constant := (9037423331342893938534360618223544876476008761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5927464831192640109/1000000000000000000)
  centralHi := (592746483119264010901/100000000000000000000)
  directionLo := (297422353659950585147/50000000000000000000)
  directionHi := (118968941463980234059/20000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree143.table
  base := (34107659337504384760669055696719148680601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4695879454442785604980831959403434479250000000000)
      constant := (184756681807149325281150626260662186468481245223535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree143.table
  base := (170538296687521921031895635930873599229767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1565702935565890509230336659119566378500000000000)
      constant := (61616545717902619577025332610342212680263020550623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297422353659950585147/50000000000000000000)
  centralHi := (118968941463980234059/20000000000000000000)
  directionLo := (37308472270192333517/6250000000000000000)
  directionHi := (596935556323077336273/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree144.table
  base := (173982789861665606272085338703393597170301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1576233985362197200426131085378026521000000000000)
      constant := (62464389972676202519612579201322005368449383940869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree144.table
  base := (543696218317705012722646734941726266253/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-394161658767532734180114143480612755250000000000)
      constant := (15623952464154050110893840317603764535050518140560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37308472270192333517/6250000000000000000)
  centralHi := (596935556323077336273/100000000000000000000)
  directionLo := (37438694209823335067/6250000000000000000)
  directionHi := (599019107357173361073/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree145.table
  base := (177460368707262163482377497231589562717219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1587174819243465865858651517621574882250000000000)
      constant := (63349469419161755855254922539502769977063482750011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree145.table
  base := (177460368707262161734752020087217284983221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4762771003723114092631729466176006990500000000000)
      constant := (190143981301620512475239547937657747447594464573047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37438694209823335067/6250000000000000000)
  centralHi := (599019107357173361073/100000000000000000000)
  directionLo := (30054771815604744939/5000000000000000000)
  directionHi := (601095436312094898781/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree146.table
  base := (180971033224315526609157937777374973092521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4794346959374203593873515849595369730500000000000)
      constant := (192722396825519472300236111080900656333925399988147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree146.table
  base := (90485516612157762610741209703154435828679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-799267017039305895850348201764110153000000000000)
      constant := (32136548724837293193991011538332154573371249686751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30054771815604744939/5000000000000000000)
  centralHi := (601095436312094898781/100000000000000000000)
  directionLo := (603164617771525690231/100000000000000000000)
  directionHi := (75395577221440711279/12500000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree147.table
  base := (184514783412829528736544004570984614417413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1609056487006003196723692382108671604750000000000)
      constant := (65138378540710461531202815473845651252339467122797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree147.table
  base := (184514783412829527634732985946834977393487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1609477733582852219190816318331104948500000000000)
      constant := (65171120904019501409672331852141205340284205419303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603164617771525690231/100000000000000000000)
  centralHi := (75395577221440711279/12500000000000000000)
  directionLo := (121045345008837681349/20000000000000000000)
  directionHi := (302613362522094203373/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree148.table
  base := (188091619272807907895193384703028061298453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1619997320887271862156212814352219966000000000000)
      constant := (66042208215773721079773097910491217289603453918557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree148.table
  base := (37618323854561581404079714925130783007633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4861264299261277940042808699401968773000000000000)
      constant := (198226192390724906464537129622509397166356173549655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121045345008837681349/20000000000000000000)
  centralHi := (302613362522094203373/50000000000000000000)
  directionLo := (75910228774268765403/12500000000000000000)
  directionHi := (24291273207766004929/4000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree149.table
  base := (7668061632170172400084468879588797808017/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4892814464305621582766199739787304981750000000000)
      constant := (200856863901088963117771532681884963034743458115475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree149.table
  base := (191701540804254309307590601899383331986871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1631365132591333074171056147936874233500000000000)
      constant := (66985927128341040250474536819605177347748449141199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75910228774268765403/12500000000000000000)
  centralHi := (24291273207766004929/4000000000000000000)
  directionLo := (609330004070207865703/100000000000000000000)
  directionHi := (76166250508775983213/12500000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree150.table
  base := (195344548007172291703237210356920188637263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1641878988649809193021253678839316688500000000000)
      constant := (67868617794478311772362612413801912391396773777447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree150.table
  base := (39068909601434458230372928788347017499781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1642308832095573501661176062739758876000000000000)
      constant := (67902709898317766059402554435959473501589282114945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609330004070207865703/100000000000000000000)
  centralHi := (76166250508775983213/12500000000000000000)
  directionLo := (611371316334388134727/100000000000000000000)
  directionHi := (76421414541798516841/12500000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree151.table
  base := (199020640881565323119947056882651106135201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1652819822531077858453774111082865049750000000000)
      constant := (68791197698119742416594554234984783588512945508969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree151.table
  base := (39804128176313064536447596824032345758119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4959757594799441787453887932627930555500000000000)
      constant := (206477237320515586157729297778910114055114722431665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611371316334388134727/100000000000000000000)
  centralHi := (76421414541798516841/12500000000000000000)
  directionLo := (613405835489592839243/100000000000000000000)
  directionHi := (153351458872398209811/25000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree152.table
  base := (202729819427436790501230269627624069679797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-4991281969237039571658883629979240233000000000000)
      constant := (209160083033861982765432890372376909671401104217079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree152.table
  base := (50682454856859197538442151235177465085527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-416049057776013589160353973086382040250000000000)
      constant := (17438758688475844044985017356930383584852661774063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613405835489592839243/100000000000000000000)
  centralHi := (153351458872398209811/25000000000000000000)
  directionLo := (76929203613302835217/12500000000000000000)
  directionHi := (615433628906422681737/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree153.table
  base := (206472083644789998783702314395892398514391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1674701490293615189318814975569961772250000000000)
      constant := (70655107733981114086472849365023587182755687992079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree153.table
  base := (51618020911197499626973167908959188112367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-418784982652073696032883951787103200875000000000)
      constant := (17672644209878088810005684035654370424344220210023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76929203613302835217/12500000000000000000)
  centralHi := (615433628906422681737/100000000000000000000)
  directionLo := (123490952569841542017/20000000000000000000)
  directionHi := (308727381424603855043/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree154.table
  base := (105123716766814087030968867749310502220691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-842821162087441927375667703906755066750000000000)
      constant := (35798218933100573796312298744111359601685484856779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree154.table
  base := (42049486706725634768602740224184068880897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-5058250890337605634864967165853892338000000000000)
      constant := (214897116090996534744769111502121971234542135873895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123490952569841542017/20000000000000000000)
  centralHi := (308727381424603855043/50000000000000000000)
  directionLo := (309734651250636745597/50000000000000000000)
  directionHi := (123893860500254698239/20000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree155.table
  base := (214055869093954465971796623838279343024977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-5089749474168457560551567520171175484250000000000)
      constant := (217632054223842418118926825523772087881320124123339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree155.table
  base := (214055869093954465798032895110703731591833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1697027329616775639111775636754182088500000000000)
      constant := (72580420326362889804060102492574912504052244299777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309734651250636745597/50000000000000000000)
  centralHi := (123893860500254698239/20000000000000000000)
  directionLo := (124295462397894032461/20000000000000000000)
  directionHi := (310738655994735081153/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree156.table
  base := (217897390325771949989543188018170805569403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1707523991937421185616376272300606856000000000000)
      constant := (73497848359220132976789539106601547433103887709107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree156.table
  base := (108948695162885974925814851200387063361279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-853985514560508033300947775778533365500000000000)
      constant := (36767360863802266728365894504996304680609418696151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124295462397894032461/20000000000000000000)
  centralHi := (310738655994735081153/50000000000000000000)
  directionLo := (311739427203995237373/50000000000000000000)
  directionHi := (623478854407990474747/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree157.table
  base := (221771997229083629649617928292284150835347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1718464825818689851048896704544155217250000000000)
      constant := (74457928720019170934621664088296297369514067193643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree157.table
  base := (221771997229083629540162703667917352833659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-5156744185875769482276046399079854120500000000000)
      constant := (223485828702171455210561595599831507842065470985113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311739427203995237373/50000000000000000000)
  centralHi := (623478854407990474747/100000000000000000000)
  directionLo := (62547399184150185841/10000000000000000000)
  directionHi := (625473991841501858411/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree158.table
  base := (28209961225486554835492916876063227839023/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-1297054244774968887361062852590777683875000000000)
      constant := (56568194367758471091458854958426414955964860349322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree158.table
  base := (4513593796077848771941551439521798981167/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-864929214064748460791067690581418008000000000000)
      constant := (37731041922860393093293861372666482332621313430575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62547399184150185841/10000000000000000000)
  centralHi := (625473991841501858411/100000000000000000000)
  directionLo := (627462785387616500697/100000000000000000000)
  directionHi := (313731392693808250349/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree159.table
  base := (114810234025100621542813902143460881544977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (342788)
      previous := (171394)
      next := (171394)
      square := (1842649639200960811138974003405000000000000)
      linear := (-309780436735711495534698748492568875000000000)
      constant := (13598583066962717180795075542861814948399479057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree159.table
  base := (229620468050201243016692232188750120117851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (685576)
      previous := (342788)
      next := (342788)
      square := (3685299278401921622277948006810000000000000)
      linear := (-619723078545296315084462547513606500000000000)
      constant := (27210802621073505656424797615505826136764086891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627462785387616500697/100000000000000000000)
  centralHi := (313731392693808250349/50000000000000000000)
  directionLo := (125889059035744489613/20000000000000000000)
  directionHi := (314722647589361224033/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree160.table
  base := (29199291496001605387486536851497078498907/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-437821831865623961836614500318700075250000000000)
      constant := (19343917564893740396463004417824355171601578870566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree160.table
  base := (233594331968012843045188059623726176040253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-5255237481413933329687125632305815903000000000000)
      constant := (232243375154043794987224909046896249167361199848271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125889059035744489613/20000000000000000000)
  centralHi := (314722647589361224033/50000000000000000000)
  directionLo := (315710790201598899603/50000000000000000000)
  directionHi := (631421580403197799207/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree161.table
  base := (59400320389332493786246478309058592707867/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1444337238)
      previous := (722168619)
      next := (722168619)
      square := (7764004254773248377734066963346967500000000000)
      linear := (-1321671121007823384584233825138761496687500000000)
      constant := (58770563193859937196894388845025337042887864923569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree161.table
  base := (237601281557329975101576736216802193208099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1762689526642218204052495125571489943500000000000)
      constant := (78400025311978187755276522515546566647178584008731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315710790201598899603/50000000000000000000)
  centralHi := (631421580403197799207/100000000000000000000)
  directionLo := (79173962415753645459/12500000000000000000)
  directionHi := (633391699326029163673/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree162.table
  base := (120820658409077656832892682798716739721653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5176002836515498918489377975564645000000000000)
      linear := (-886584497612516589105749432880948511750000000000)
      constant := (39676040833455723511159836053832229928978244439357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree162.table
  base := (48328263363631062726268085648392809886721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1773633226146458631542615040374374586000000000000)
      constant := (79391845344486283538101923762625056725779201079245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79173962415753645459/12500000000000000000)
  centralHi := (633391699326029163673/100000000000000000000)
  directionLo := (63535570930885470623/10000000000000000000)
  directionHi := (635355709308854706231/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree163.table
  base := (30714304718811434115336638438806668032647/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-446027457276575460911004824501361346187500000000)
      constant := (20087415621217397720900646848427785792973123699686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree163.table
  base := (245714437750491472895362285255784202129761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (5777348952)
      previous := (2888674476)
      next := (2888674476)
      square := (31056017019092993510936267853387870000000000000)
      linear := (-5353730776952097177098204865531777685500000000000)
      constant := (241169755446616768087781266731522683047906477068827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63535570930885470623/10000000000000000000)
  centralHi := (635355709308854706231/100000000000000000000)
  directionLo := (637313666829451283107/100000000000000000000)
  directionHi := (159328416707362820777/25000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree164.table
  base := (124910322177170504359181595377600202129699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-2692575994481355763614809595373490619000000000000)
      constant := (122030240068531576055458164509868087968584593277393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree164.table
  base := (49964128870868201739335595971365460213781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1795520625154939486522854869980143871000000000000)
      constant := (81394244725136141419354933796218424115949575444945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637313666829451283107/100000000000000000000)
  centralHi := (159328416707362820777/25000000000000000000)
  directionLo := (639265627500684399649/100000000000000000000)
  directionHi := (12785312550013687993/2000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree165.table
  base := (253959936629706420064694628803676629250867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1805991496868839174509060162492542107250000000000)
      constant := (82363574349365861868859061987964030940331682616523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree165.table
  base := (50791987325941284009497895823425103381043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1806464324659179914012974784783028513500000000000)
      constant := (82404824073277975094820571335630056735621451381335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639265627500684399649/100000000000000000000)
  centralHi := (12785312550013687993/2000000000000000000)
  directionLo := (641211646088938977629/100000000000000000000)
  directionHi := (64121164608893897763/10000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree166.table
  base := (258132314576590150792441407081974854732529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1816932330750107839941580594736090468500000000000)
      constant := (83379905395904058984319928168924071616044310437401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree166.table
  base := (129066157288295075389395630355059331839621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-2726112036245130512254642049378869734000000000000)
      constant := (125132484789946687491075836155997640179690842767847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641211646088938977629/100000000000000000000)
  centralHi := (64121164608893897763/10000000000000000000)
  directionLo := (321575888266024106453/50000000000000000000)
  directionHi := (643151776532048212907/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree167.table
  base := (131168889097497295552848706629943952996001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-2741809746947064758061151540469458244625000000000)
      constant := (126603729777953513843572933236095194910881635202507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree167.table
  base := (6558444454874864777371702821602669009543/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2588001418257749459244688987782322500000000000)
      linear := (-457087930916915192248303653597199449625000000000)
      constant := (21111185521298906240685377306691368280019727427670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321575888266024106453/50000000000000000000)
  centralHi := (643151776532048212907/100000000000000000000)
  directionLo := (322543035978368564231/50000000000000000000)
  directionHi := (645086071956737128463/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree168.table
  base := (266576327484922079083424580722629152427403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1838813998512645170806621459223187191000000000000)
      constant := (85431317717560745710638380274683569325698786711107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree168.table
  base := (266576327484922079074833497601790584614077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1839295423171901196483334529191682441000000000000)
      constant := (85474080748971508108488808696347720583744130099013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell151.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322543035978368564231/50000000000000000000)
  centralHi := (645086071956737128463/100000000000000000000)
  directionLo := (64701458469559678247/10000000000000000000)
  directionHi := (647014584695596782471/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree169.table
  base := (270847962446374902130104171769955327167027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10352005673030997836978755951129290000000000000)
      linear := (-1849754832393913836239141891466735552250000000000)
      constant := (86466398992679300819123228552282273771361956047563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree169.table
  base := (135423981223187451061644474520969666424661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (2888674476)
      previous := (1444337238)
      next := (1444337238)
      square := (15528008509546496755468133926693935000000000000)
      linear := (-2775358684014212435960181665991850625250000000000)
      constant := (129764508776938210231992277420289310607262351583127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell151.Kernel169
