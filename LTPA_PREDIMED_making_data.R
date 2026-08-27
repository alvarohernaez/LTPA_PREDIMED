rm(list=ls())

# EXECUTE ALL - OPEN INSTALLED PACKAGES

library(acepack)
library(arm)
library(backports)
library(base64enc)
library(bitops)
library(boot)
library(car)
library(caTools)
library(checkmate)
library(chron)
library(cobalt)
library(colorspace)
library(compareGroups)
library(data.table)
library(DescTools)
library(dichromat)
library(digest)
library(dplyr)
library(evaluate)
library(foreign)
library(Formula)
library(gam)
library(ggplot2)
library(ggpubr)
library(gplots)
library(gratia)
library(gridExtra)
library(gtable)
library(haven)
library(highr)
library(Hmisc)
library(htmlTable)
library(htmltools)
library(htmlwidgets)
library(icenReg)
library(irr)
library(jsonlite)
library(keras)
library(knitr)
library(labeling)
library(latticeExtra)
library(lazyeval)
library(lme4)
library(lmerTest)
library(lmtest)
library(MASS)
library(magrittr)
library(markdown)
library(MatrixModels)
library(meta)
library(metafor)
library(mgcv)
library(missRanger)
library(mime)
library(minqa)
library(MuMIn)
library(munsell)
library(nephro)
library(nlme)
library(pbkrtest)
library(plotrix)
library(plyr)
library(psy)
library(purrr)
library(quantreg)
library(RColorBrewer)
library(Rcpp)
library(RcppEigen)
library(rlang)
library(ROCR)
library(RODBC)
library(reshape2)
library(sandwich)
library(scales)
library(smoothHR)
library(SparseM)
library(standardize)
library(stringi)
library(stringr)
library(survival)
library(survminer)
library(tibble)
library(tidyr)
library(vcd)
library(viridis)
library(viridisLite)
library(WeightIt)
library(yaml)

# OPEN PRE-GENERATED FUNCTIONS

RutinesLocals<- "D:/R/Rutinas"
source(file.path(RutinesLocals,"carrega.llibreria.r"))
source(file.path(RutinesLocals,"merge2.r"))
source(file.path(RutinesLocals,"fix2.r"))
source(file.path(RutinesLocals,"table2.r"))
source(file.path(RutinesLocals,"subset2.r"))
source(file.path(RutinesLocals,"format2.r"))
source(file.path(RutinesLocals,"order2.r"))
source(file.path(RutinesLocals,"intervals.r"))

# OPEN MY OWN FUNCTIONS TO PUT RESULTS IN NICE FORMAT ("guapa")

guapa<-function(x)
{
  redondeo<-ifelse(abs(x)<0.00001,signif(x,1),
                   ifelse(abs(x)<0.0001,signif(x,1),
                          ifelse(abs(x)<0.001,signif(x,1),
                                 ifelse(abs(x)<0.1,sprintf("%.3f",round(x,3)),
                                        ifelse(abs(x)<1,sprintf("%.2f",round(x,2)),
                                               ifelse(abs(x)<10,sprintf("%.2f",round(x,2)),
                                                      ifelse(abs(x)<100,sprintf("%.1f",round(x,1)),
                                                             ifelse(abs(x)>=100,round(x,0),round(x,0)))))))))
  return(redondeo)
}

ic_guapa<-function(x,y,z)
{
  ic<-paste(x," [",y,"; ",z,"]",sep="")
  return(ic)
}

ic_guapa2<-function(x,y,z)
{
  ic<-paste(x," (",y," to ",z,")",sep="")
  return(ic)
}

pval_guapa<-function(x)
{
  pval<-ifelse(x<0.00001,"<0.00001",
               ifelse(x<0.001,"<0.001",
                      ifelse(abs(x)<0.01,sprintf("%.3f",round(x,3)),
                             ifelse(abs(x)<0.1,sprintf("%.3f",round(x,3)),
                                    ifelse(abs(x)<1,sprintf("%.3f",round(x,3)),guapa(x))))))
  return(pval)
}

pval_guapa2<-function(x)
{
  pval<-ifelse(x<0.00001," < 0.00001",
               ifelse(x<0.001," < 0.001",
                      ifelse(abs(x)<0.01,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),
                             ifelse(abs(x)<0.1,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),
                                    ifelse(abs(x)<1,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),guapa(x))))))
  return(pval)
}

mean_ic_guapa <- function(x, na.rm=FALSE) 
{
  if (na.rm) x <- na.omit(x)
  se<-sqrt(var(x)/length(x))
  z<-qnorm(1-0.05/2)
  media<-mean(x)
  ic95a<-guapa(media-(z*se))
  ic95b<-guapa(media+(z*se))
  media<-guapa(media)
  ic_ok<-ic_guapa(media,ic95a,ic95b)
  return(ic_ok)
}

mean_sd_guapa <- function(x) 
{
  media<-guapa(mean(x, na.rm=TRUE))
  sd<-guapa(sd(x, na.rm=TRUE))
  end<-paste(media," (",sd,")",sep="")
  return(end)
}

beta_se_ic_guapa <- function(x, y) 
{
  z<-qnorm(1-0.05/2)
  ic95a<-guapa(x-(z*y))
  ic95b<-guapa(x+(z*y))
  media<-guapa(x)
  ic_ok<-ic_guapa(media,ic95a,ic95b)
  return(ic_ok)
}

beta_se_ic_guapa2 <- function(x, y) 
{
  z<-qnorm(1-0.05/2)
  ic95a<-guapa(x-(z*y))
  ic95b<-guapa(x+(z*y))
  media<-guapa(x)
  ic_ok<-ic_guapa2(media,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-guapa(exp(x))
  ic95a<-guapa(exp(x-(z*y)))
  ic95b<-guapa(exp(x+(z*y)))
  ic_ok<-ic_guapa(hr,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa2 <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-guapa(exp(x))
  ic95a<-guapa(exp(x-(z*y)))
  ic95b<-guapa(exp(x+(z*y)))
  ic_ok<-ic_guapa2(hr,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa3 <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-round(exp(x),3)
  ic95a<-round(exp(x-(z*y)),3)
  ic95b<-round(exp(x+(z*y)),3)
  ic_ok<-ic_guapa2(hr,ic95a,ic95b)
  return(ic_ok)
}

header.true <- function(df)
{
  names(df) <- as.character(unlist(df[1,]))
  df[-1,]
}

z<-qnorm(1-0.05/2)
se <- function(x) sqrt(var(x) / length(x))

closest<-function(xv,sv){
  xv[which(abs(xv-sv)==min(abs(xv-sv)))] }

options(scipen=999)

setwd("D:/Artículos/Eleonora - LTPA PREDIMED")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Data")


### CREATION OF DATABASE - EXTRACTION OF INFORMATION FROM DIFFERENT SOURCES ###
###############################################################################

# This (below) is the database with all biomarkers

load("D:/Artículos/Accepted/Montse - MedDiet and lipid profile/Data/predimed_bbdd.RData")

dat<-rename.vars(dat,
                 from=c("diabetes0","hipercol0","hta0","edad0","escolar01","hipertrigli01","kcal_total01",
                        "imc01","imc03","imc04","imc05","imc06","imc07","imc08","imc09","imc10",
                        "cintura01","cintura03","cintura04","cintura05","cintura06","cintura07","cintura08","cintura09","cintura10",
                        "pas01","pas03","pas04","pas05","pas06","pas07","pas08","pas09","pas10",
                        "pad01","pad03","pad04","pad05","pad06","pad07","pad08","pad09","pad10",
                        "ca_col01","ca_col03","ca_col04","ca_col05","ca_col06","ca_col07","ca_col08","ca_col09","ca_col10",
                        "ca_hdl01","ca_hdl03","ca_hdl04","ca_hdl05","ca_hdl06","ca_hdl07","ca_hdl08","ca_hdl09","ca_hdl10",
                        "ca_ldl01","ca_ldl03","ca_ldl04","ca_ldl05","ca_ldl06","ca_ldl07","ca_ldl08","ca_ldl09","ca_ldl10",
                        "ca_tg01","ca_tg03","ca_tg04","ca_tg05","ca_tg06","ca_tg07","ca_tg08","ca_tg09","ca_tg10",
                        "ca_gluco01","ca_gluco03","ca_gluco04","ca_gluco05","ca_gluco06","ca_gluco07","ca_gluco08","ca_gluco09","ca_gluco10",
                        "hba1c1","hba1c3","hba1c4","hba1c5","hba1c6","hba1c7","hba1c8","hba1c9","hba1c10",
                        "plqt01","plqt03","plqt04","plqt05","plqt06","plqt07","plqt08","plqt09","plqt10",
                        "f_htatot01","f_htatot03","f_htatot04","f_htatot05","f_htatot06","f_htatot07","f_htatot08","f_htatot09","f_htatot10",
                        "f_hipocoltot01","f_hipocoltot03","f_hipocoltot04","f_hipocoltot05","f_hipocoltot06","f_hipocoltot07","f_hipocoltot08","f_hipocoltot09","f_hipocoltot10",
                        "f_hipotrigtot01","f_hipotrigtot03","f_hipotrigtot04","f_hipotrigtot05","f_hipotrigtot06","f_hipotrigtot07","f_hipotrigtot08","f_hipotrigtot09","f_hipotrigtot10",
                        "f_antidiabettot01","f_antidiabettot03","f_antidiabettot04","f_antidiabettot05","f_antidiabettot06","f_antidiabettot07","f_antidiabettot08","f_antidiabettot09","f_antidiabettot10"),
                 to=c("diabetes00","hipercol00","hta00","edad00","escolar00","hipertg00","kcal00",
                      "bmi00","bmi01","bmi02","bmi03","bmi04","bmi05","bmi06","bmi07","bmi08",
                      "wc00","wc01","wc02","wc03","wc04","wc05","wc06","wc07","wc08",
                      "sbp00","sbp01","sbp02","sbp03","sbp04","sbp05","sbp06","sbp07","sbp08",
                      "dbp00","dbp01","dbp02","dbp03","dbp04","dbp05","dbp06","dbp07","dbp08",
                      "tc00","tc01","tc02","tc03","tc04","tc05","tc06","tc07","tc08",
                      "hdlc00","hdlc01","hdlc02","hdlc03","hdlc04","hdlc05","hdlc06","hdlc07","hdlc08",
                      "ldlc00","ldlc01","ldlc02","ldlc03","ldlc04","ldlc05","ldlc06","ldlc07","ldlc08",
                      "tg00","tg01","tg02","tg03","tg04","tg05","tg06","tg07","tg08",
                      "gluco00","gluco01","gluco02","gluco03","gluco04","gluco05","gluco06","gluco07","gluco08",
                      "hb1ac00","hb1ac01","hb1ac02","hb1ac03","hb1ac04","hb1ac05","hb1ac06","hb1ac07","hb1ac08",
                      "plat00","plat01","plat02","plat03","plat04","plat05","plat06","plat07","plat08",
                      "f_hta_00","f_hta_01","f_hta_02","f_hta_03","f_hta_04","f_hta_05","f_hta_06","f_hta_07","f_hta_08",
                      "f_chol_00","f_chol_01","f_chol_02","f_chol_03","f_chol_04","f_chol_05","f_chol_06","f_chol_07","f_chol_08",
                      "f_tg_00","f_tg_01","f_tg_02","f_tg_03","f_tg_04","f_tg_05","f_tg_06","f_tg_07","f_tg_08",
                      "f_gluco_00","f_gluco_01","f_gluco_02","f_gluco_03","f_gluco_04","f_gluco_05","f_gluco_06","f_gluco_07","f_gluco_08"))

dat$ldlc_hdlc00<-dat$ldlc00/dat$hdlc00
dat$ldlc_hdlc01<-dat$ldlc01/dat$hdlc01
dat$ldlc_hdlc02<-dat$ldlc02/dat$hdlc02
dat$ldlc_hdlc03<-dat$ldlc03/dat$hdlc03
dat$ldlc_hdlc04<-dat$ldlc04/dat$hdlc04
dat$ldlc_hdlc05<-dat$ldlc05/dat$hdlc05
dat$ldlc_hdlc06<-dat$ldlc06/dat$hdlc06
dat$ldlc_hdlc07<-dat$ldlc07/dat$hdlc07
dat$ldlc_hdlc08<-dat$ldlc08/dat$hdlc08

dat$pp00<-dat$sbp00-dat$dbp00
dat$pp01<-dat$sbp01-dat$dbp01
dat$pp02<-dat$sbp02-dat$dbp02
dat$pp03<-dat$sbp03-dat$dbp03
dat$pp04<-dat$sbp04-dat$dbp04
dat$pp05<-dat$sbp05-dat$dbp05
dat$pp06<-dat$sbp06-dat$dbp06
dat$pp07<-dat$sbp07-dat$dbp07
dat$pp08<-dat$sbp08-dat$dbp08

dat$whtr00<-dat$wc00/(dat$altura01*100)
dat$whtr01<-dat$wc01/(dat$altura01*100)
dat$whtr02<-dat$wc02/(dat$altura01*100)
dat$whtr03<-dat$wc03/(dat$altura01*100)
dat$whtr04<-dat$wc04/(dat$altura01*100)
dat$whtr05<-dat$wc05/(dat$altura01*100)
dat$whtr06<-dat$wc06/(dat$altura01*100)
dat$whtr07<-dat$wc07/(dat$altura01*100)
dat$whtr08<-dat$wc08/(dat$altura01*100)

dat$ethnic<-0
vars<-c("creatsu1","creatsu3","creatsu4","creatsu5","creatsu6","creatsu7","creatsu8","creatsu9","creatsu10")
dat[vars] <- lapply(dat[vars], function(x) ifelse(x > 10, NA, x))
dat$egfr00<-CKDEpi.creat(dat$creatsu1, dat$sexo, (dat$edad0+0), dat$ethnic)
dat$egfr01<-CKDEpi.creat(dat$creatsu3, dat$sexo, (dat$edad0+1), dat$ethnic)
dat$egfr02<-CKDEpi.creat(dat$creatsu4, dat$sexo, (dat$edad0+2), dat$ethnic)
dat$egfr03<-CKDEpi.creat(dat$creatsu5, dat$sexo, (dat$edad0+3), dat$ethnic)
dat$egfr04<-CKDEpi.creat(dat$creatsu6, dat$sexo, (dat$edad0+4), dat$ethnic)
dat$egfr05<-CKDEpi.creat(dat$creatsu7, dat$sexo, (dat$edad0+5), dat$ethnic)
dat$egfr06<-CKDEpi.creat(dat$creatsu8, dat$sexo, (dat$edad0+6), dat$ethnic)
dat$egfr07<-CKDEpi.creat(dat$creatsu9, dat$sexo, (dat$edad0+7), dat$ethnic)
dat$egfr08<-CKDEpi.creat(dat$creatsu10, dat$sexo, (dat$edad0+8), dat$ethnic)

dat$nlr00<-dat$neutros01/dat$linfos01
dat$nlr01<-dat$neutros03/dat$linfos03
dat$nlr02<-dat$neutros04/dat$linfos04
dat$nlr03<-dat$neutros05/dat$linfos05
dat$nlr04<-dat$neutros06/dat$linfos06
dat$nlr05<-dat$neutros07/dat$linfos07
dat$nlr06<-dat$neutros08/dat$linfos08
dat$nlr07<-dat$neutros09/dat$linfos09
dat$nlr08<-dat$neutros10/dat$linfos10

dat[c("hb1ac00","hb1ac01","hb1ac02","hb1ac03","hb1ac04","hb1ac05","hb1ac06","hb1ac07","hb1ac08")] <- lapply(
  dat[c("hb1ac00","hb1ac01","hb1ac02","hb1ac03","hb1ac04","hb1ac05","hb1ac06","hb1ac07","hb1ac08")], function(x) {
  x[x > 15] <- NA
  x})

dat$tobacco00<-with(dat,ifelse(tabaco01==1,1,
                               ifelse(tabaco01==2,2,
                                      ifelse(tabaco01==3,2,
                                             ifelse(tabaco01==4,2,
                                                    ifelse(tabaco01==5,0,
                                                           ifelse(tabaco01==9,NA,NA)))))))
# 0=Never smokers, 1=Smokers, 2=Ex-smokers

temp<-dat[,c("id","nodo","grup_int","sexo","edad00","diabetes00","hipercol00","hta00","tobacco00",
             "hipertg00","escolar00","kcal00",
             "prop_score01","prop_score02","idcluster2","parejas","f_ultcontact_nejm",
             "bmi00","bmi01","bmi02","bmi03","bmi04","bmi05","bmi06","bmi07","bmi08",
             "wc00","wc01","wc02","wc03","wc04","wc05","wc06","wc07","wc08",
             "whtr00","whtr01","whtr02","whtr03","whtr04","whtr05","whtr06","whtr07","whtr08",
             "sbp00","sbp01","sbp02","sbp03","sbp04","sbp05","sbp06","sbp07","sbp08",
             "dbp00","dbp01","dbp02","dbp03","dbp04","dbp05","dbp06","dbp07","dbp08",
             "pp00","pp01","pp02","pp03","pp04","pp05","pp06","pp07","pp08",
             "tc00","tc01","tc02","tc03","tc04","tc05","tc06","tc07","tc08",
             "hdlc00","hdlc01","hdlc02","hdlc03","hdlc04","hdlc05","hdlc06","hdlc07","hdlc08",
             "ldlc00","ldlc01","ldlc02","ldlc03","ldlc04","ldlc05","ldlc06","ldlc07","ldlc08",
             "ldlc_hdlc00","ldlc_hdlc01","ldlc_hdlc02","ldlc_hdlc03","ldlc_hdlc04","ldlc_hdlc05","ldlc_hdlc06","ldlc_hdlc07","ldlc_hdlc08",
             "tg00","tg01","tg02","tg03","tg04","tg05","tg06","tg07","tg08",
             "gluco00","gluco01","gluco02","gluco03","gluco04","gluco05","gluco06","gluco07","gluco08",
             "hb1ac00","hb1ac01","hb1ac02","hb1ac03","hb1ac04","hb1ac05","hb1ac06","hb1ac07","hb1ac08",
             "egfr00","egfr01","egfr02","egfr03","egfr04","egfr05","egfr06","egfr07","egfr08",
             "nlr00","nlr01","nlr02","nlr03","nlr04","nlr05","nlr06","nlr07","nlr08",
             "plat00","plat01","plat02","plat03","plat04","plat05","plat06","plat07","plat08",
             "f_hta_00","f_hta_01","f_hta_02","f_hta_03","f_hta_04","f_hta_05","f_hta_06","f_hta_07","f_hta_08",
             "f_chol_00","f_chol_01","f_chol_02","f_chol_03","f_chol_04","f_chol_05","f_chol_06","f_chol_07","f_chol_08",
             "f_tg_00","f_tg_01","f_tg_02","f_tg_03","f_tg_04","f_tg_05","f_tg_06","f_tg_07","f_tg_08",
             "f_gluco_00","f_gluco_01","f_gluco_02","f_gluco_03","f_gluco_04","f_gluco_05","f_gluco_06","f_gluco_07","f_gluco_08")]

# This (below) is the database that has LTPA and follow-up times

dat<-spss.get("D:/Artículos/Accepted/Montse - MedDiet and lipid profile/Data/bbdd_predimed_20101201.sav",
              use.value.labels=FALSE,to.data.frame=TRUE,allow="_")

dat<-rename.vars(dat,
                 from=c("getota_1","getota_3","getota_4","getota_5","getota_6","getota_7","getota_8","getota_9","getota_10",
                        "datinclu","datseg3","datseg4","datseg5","datseg6","datseg7","datseg8","datseg9","datseg10"),
                 to=c("ltpa00","ltpa01","ltpa02","ltpa03","ltpa04","ltpa05","ltpa06","ltpa07","ltpa08",
                      "seg00","seg01","seg02","seg03","seg04","seg05","seg06","seg07","seg08"))


# ge4_5_5a_x = moderate LTPA in METs.min/day; ge6_12a_x = vigorous LTPA in METs.min/day

dat$mvltpa00<-dat$ge4_5_5a_1+dat$ge6_12a_1
dat$mvltpa01<-dat$ge4_5_5a_3+dat$ge6_12a_3
dat$mvltpa02<-dat$ge4_5_5a_4+dat$ge6_12a_4
dat$mvltpa03<-dat$ge4_5_5a_5+dat$ge6_12a_5
dat$mvltpa04<-dat$ge4_5_5a_6+dat$ge6_12a_6
dat$mvltpa05<-dat$ge4_5_5a_7+dat$ge6_12a_7
dat$mvltpa06<-dat$ge4_5_5a_8+dat$ge6_12a_8
dat$mvltpa07<-dat$ge4_5_5a_9+dat$ge6_12a_9
dat$mvltpa08<-dat$ge4_5_5a_10+dat$ge6_12a_10


# LONGITUDINAL AVERAGE OF LTPA
# Both LTPA and MVLTPA are in METs.min/day

dat$ltpalong<-rowMeans(dat[,c("ltpa00","ltpa01","ltpa02","ltpa03","ltpa04","ltpa05","ltpa06","ltpa07","ltpa08")], na.rm=TRUE)
dat$mvltpalong<-rowMeans(dat[,c("mvltpa00","mvltpa01","mvltpa02","mvltpa03","mvltpa04","mvltpa05","mvltpa06","mvltpa07","mvltpa08")], na.rm=TRUE)

# TRANSFORM SPSS-FORMAT DATES INTO OK-FORMAT DATES

vars01<-c("seg00","seg01","seg02","seg03","seg04","seg05","seg06","seg07","seg08")

for (i in 1:length(vars01)) {
  dat[, vars01[i]] <- chron(
    dates. = as.numeric(as.Date(dat[, vars01[i]]/86400, origin = "1582-10-14")),
    out.format = c(dates = "d/m/y", times = "h:m:s")
  )
  
  dat[, vars01[i]] <- with(
    dat,
    ifelse(as.numeric(dat[, vars01[i]]) > as.numeric(as.Date("2010-12-01")), NA, dat[, vars01[i]])
  )
  
  dat[, vars01[i]] <- chron(
    dates. = as.numeric(as.Date(as.numeric(dat[, vars01[i]]), origin = "1970-01-01")),
    out.format = c(dates = "d/m/y", times = "h:m:s")
  )
}


# GENERATE DATES OF BIRTHS OF PARTICIPANTS

dat$anonac<-dat$anonac+1900
dat$birthday<-paste(dat$anonac,dat$mesnac,dat$dianac,sep="-")
dat$birthday<-chron(as.numeric(as.Date(dat$birthday,origin="1970-01-01")),format="d/m/y")

# CALCULATE THE EXACT AGE OF PARTICIPANTS AT ALL VISITS

vars01<-c("seg00","seg01","seg02","seg03","seg04","seg05","seg06","seg07","seg08")
vars02<-c("age00","age01","age02","age03","age04","age05","age06","age07","age08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-(dat[,vars01[i]]-dat$birthday)/365.25
}

# CREATE TEMPORARY DATABASE temp2 WITH SOME VARIABLES OF dat

temp2<-dat[,c("id",
              "ltpa00","ltpa01","ltpa02","ltpa03","ltpa04","ltpa05","ltpa06","ltpa07","ltpa08","ltpalong",
              "mvltpa00","mvltpa01","mvltpa02","mvltpa03","mvltpa04","mvltpa05","mvltpa06","mvltpa07","mvltpa08","mvltpalong",
              "seg00","seg01","seg02","seg03","seg04","seg05","seg06","seg07","seg08",
              "age00","age01","age02","age03","age04","age05","age06","age07","age08")]

# ADHERENCE TO MEDITERRANEAN DIET IN ALL STUDY VISITS

p14<-spss.get("D:/Artículos/Accepted/Montse - MedDiet and lipid profile/Data/pred_p14.sav",
              use.value.labels=FALSE,to.data.frame=TRUE,allow="_")

p14<-rename.vars(p14,
                 from=c("p14_01_nejm","p14_03_nejm","p14_04_nejm","p14_05_nejm",
                        "p14_06_nejm","p14_07_nejm","p14_08_nejm","p14totm_9","p14totm_10"),
                 to=c("dmed00","dmed01","dmed02","dmed03","dmed04","dmed05","dmed06","dmed07","dmed08"))

p14$dmed07<-with(p14,ifelse(dmed07==0,NA,dmed07))
p14$dmed08<-with(p14,ifelse(dmed08==0,NA,dmed08))
p14$dmedlong<-rowMeans(p14[,c("dmed00","dmed01","dmed02","dmed03","dmed04","dmed05","dmed06","dmed07","dmed08")], na.rm=TRUE)

temp3<-p14[,c("id",
              "dmed00","dmed01","dmed02","dmed03","dmed04","dmed05","dmed06","dmed07","dmed08","dmedlong")]

# MERGE ALL temp DATABASES AND ERASE THE UNUSEFUL DATASETS

dat<-merge2(temp,temp2,by.id=c("id"),all.x=TRUE,sort=FALSE)
dat<-merge2(dat,temp3,by.id=c("id"),all.x=TRUE,sort=FALSE)
temp<-NULL
temp2<-NULL
temp3<-NULL
p14<-NULL

# IF SOMEONE COMES TO A VISIT, THEY HAVE BMI VALUES; IF THEY DON'T COME, THEY DON'T HAVE THEM

vars00<-c("age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08",
          "age00","age01","age02","age03","age04","age05","age06","age07","age08")
vars01<-c("bmi00","bmi01","bmi02","bmi03","bmi04","bmi05","bmi06","bmi07","bmi08",
          "wc00","wc01","wc02","wc03","wc04","wc05","wc06","wc07","wc08",
          "whtr00","whtr01","whtr02","whtr03","whtr04","whtr05","whtr06","whtr07","whtr08",
          "sbp00","sbp01","sbp02","sbp03","sbp04","sbp05","sbp06","sbp07","sbp08",
          "dbp00","dbp01","dbp02","dbp03","dbp04","dbp05","dbp06","dbp07","dbp08",
          "pp00","pp01","pp02","pp03","pp04","pp05","pp06","pp07","pp08",
          "tc00","tc01","tc02","tc03","tc04","tc05","tc06","tc07","tc08",
          "hdlc00","hdlc01","hdlc02","hdlc03","hdlc04","hdlc05","hdlc06","hdlc07","hdlc08",
          "ldlc00","ldlc01","ldlc02","ldlc03","ldlc04","ldlc05","ldlc06","ldlc07","ldlc08",
          "ldlc_hdlc00","ldlc_hdlc01","ldlc_hdlc02","ldlc_hdlc03","ldlc_hdlc04","ldlc_hdlc05","ldlc_hdlc06","ldlc_hdlc07","ldlc_hdlc08",
          "tg00","tg01","tg02","tg03","tg04","tg05","tg06","tg07","tg08",
          "gluco00","gluco01","gluco02","gluco03","gluco04","gluco05","gluco06","gluco07","gluco08",
          "hb1ac00","hb1ac01","hb1ac02","hb1ac03","hb1ac04","hb1ac05","hb1ac06","hb1ac07","hb1ac08",
          "egfr00","egfr01","egfr02","egfr03","egfr04","egfr05","egfr06","egfr07","egfr08",
          "nlr00","nlr01","nlr02","nlr03","nlr04","nlr05","nlr06","nlr07","nlr08",
          "plat00","plat01","plat02","plat03","plat04","plat05","plat06","plat07","plat08",
          "dmed00","dmed01","dmed02","dmed03","dmed04","dmed05","dmed06","dmed07","dmed08",
          "ltpa00","ltpa01","ltpa02","ltpa03","ltpa04","ltpa05","ltpa06","ltpa07","ltpa08",
          "mvltpa00","mvltpa01","mvltpa02","mvltpa03","mvltpa04","mvltpa05","mvltpa06","mvltpa07","mvltpa08",
          "f_hta_00","f_hta_01","f_hta_02","f_hta_03","f_hta_04","f_hta_05","f_hta_06","f_hta_07","f_hta_08",
          "f_chol_00","f_chol_01","f_chol_02","f_chol_03","f_chol_04","f_chol_05","f_chol_06","f_chol_07","f_chol_08",
          "f_tg_00","f_tg_01","f_tg_02","f_tg_03","f_tg_04","f_tg_05","f_tg_06","f_tg_07","f_tg_08",
          "f_gluco_00","f_gluco_01","f_gluco_02","f_gluco_03","f_gluco_04","f_gluco_05","f_gluco_06","f_gluco_07","f_gluco_08")

for(i in 1:length(vars01))
{
  dat[,vars01[i]]<-with(dat,ifelse(is.na(dat[,vars00[i]]),NA,dat[,vars01[i]]))
}

# OTHER TRANSFORMATIONS

dat$obesity00<-with(dat,ifelse(bmi00<25,0,
                               ifelse(bmi00<30,1,
                                      ifelse(bmi00>=30,2,NA))))
dat$adobesity00<-with(dat,ifelse(wc00>=89 & sexo==1,1,
                                 ifelse(wc00>=103 & sexo==0,1,0)))
dat$c_adip00<-with(dat,ifelse(whtr00>=0.6,1,0))
dat$grup_int2<-with(dat,ifelse(grup_int==3,0,1))
dat$tobacco200<-with(dat,ifelse(tobacco00==0,0,1))
dat$obesity200<-with(dat,ifelse(obesity00==2,1,0))

# We create a variable which =1 when the participant has only the baseline visit
dat <- dat %>%
  dplyr::mutate(age_na = as.integer(rowSums(is.na(dplyr::pick(age01:age08))) == 8))

# We create "excl" for sensitivity analyses
dat$excl<-with(dat,ifelse(parejas==1 | nodo==4 | nodo==1,1,0))

# We create categories of MVLTPA (mvltpalong)
dat$mvltpa_cat2<-with(dat,ifelse(mvltpalong==0,0,
                                 ifelse(mvltpalong<100,0,
                                        ifelse(mvltpalong<200,1,
                                               ifelse(mvltpalong>=200,1,NA)))))
dat$mvltpa_cat4<-with(dat,ifelse(mvltpalong==0,0,
                                 ifelse(mvltpalong<100,1,
                                        ifelse(mvltpalong<200,2,
                                               ifelse(mvltpalong>=200,3,NA)))))

dat[] <- lapply(dat, function(x) {
  if (inherits(x, "labelled")) {
    as.numeric(as.character(x))
  } else {
    x
  }
})

vars<-c("nodo","grup_int","tobacco00","mvltpa_cat2")
dat[vars]<-lapply(dat[vars],function(x) as.factor(x))

# Imputation of missing values in covariates (escolar00 and kcal00)

library(Hmisc)
dat_imp<-dat[,c("id","sexo","age00","grup_int","diabetes00","hipercol00",
                "hipertg00","hta00","tobacco00","bmi00","ltpa00","mvltpa00","dmed00",
                "escolar00","kcal00")]
dat_imp$escolar00 <- factor(ifelse(dat_imp$escolar00 == 9, NA, dat_imp$escolar00), levels = 1:3)
colMeans(is.na(dat_imp[, c("escolar00", "kcal00", "dmed00")])) * 100
#escolar00    kcal00     dmed00 
#1.8128105    1.0474016  0.6848395 

set.seed(1988)
imp <- aregImpute(
  ~ sexo + age00 + grup_int + diabetes00 + hipercol00 +
    hipertg00 + hta00 + tobacco00 + bmi00 +
    ltpa00 + mvltpa00 +
    dmed00 + escolar00 + kcal00,
  data = dat_imp,
  n.impute = 5)

imp.list <- lapply(1:5, function(i)
  impute.transcan(
    imp,
    imputation = i,
    data = dat_imp,
    list.out = TRUE,
    pr = FALSE
  )
)

Mode <- function(x) {
  ux <- unique(x)
  ux[which.max(tabulate(match(x, ux)))]
}

dat_imp$kcal00 <- Reduce("+", lapply(imp.list, `[[`, "kcal00")) / 5
dat_imp$dmed00 <- Reduce("+", lapply(imp.list, `[[`, "dmed00")) / 5
dat_imp$escolar00 <- apply(sapply(imp.list, `[[`, "escolar00"), 1, Mode)
dat_imp$escolar00 <- ifelse(as.numeric(as.character(dat_imp$escolar00)) == 1, 0, 1)

idx <- match(dat$id, dat_imp$id)
dat$escolar00 <- dat_imp$escolar00[idx]
dat$kcal00    <- dat_imp$kcal00[idx]
dat$dmed00    <- dat_imp$dmed00[idx]
rm(dat_imp, imp, imp.list, idx)


# STUDY FLOWCHART

dim(dat)[1] #7447
length(which(dat$nodo==12)) #-1094, we remove 1094 participants with unavailable data
dat<-subset2(dat,"nodo!=12")
dim(dat)[1] #6353
length(which(is.na(dat$age00))) #0, Everyone has age at baseline
length(which(dat$age00<60)) #-680, we remove participants with age <60
dat<-subset2(dat,"age00>=60")
dim(dat)[1] #5673
length(which(is.na(dat$ltpa00))) #-43, we remove 43 participants without baseline LTPA
dat<-subset2(dat,"!is.na(ltpa00)")
dim(dat)[1] #5630
length(which(is.na(dat$mvltpa00))) #0, Everyone here has MVLTPA
dim(dat)[1] #5630
length(which(dat$age_na==1)) #-231, we remove 231 participants who only attended to the baseline visit
dat<-subset2(dat,"age_na!=1")
dim(dat)[1] #5399

dat <- dat %>%
  dplyr::mutate(bmi_na = as.integer(rowSums(is.na(dplyr::pick(bmi01:bmi08))) == 8))
dat <- dat %>%
  dplyr::mutate(wc_na = as.integer(rowSums(is.na(dplyr::pick(wc01:wc08))) == 8))
dat <- dat %>%
  dplyr::mutate(bp_na = as.integer(rowSums(is.na(dplyr::pick(sbp01:sbp08))) == 8))
dat <- dat %>%
  dplyr::mutate(lipids_na = as.integer(rowSums(is.na(dplyr::pick(ldlc_hdlc01:ldlc_hdlc08))) == 8))
dat <- dat %>%
  dplyr::mutate(gluco_na = as.integer(rowSums(is.na(dplyr::pick(gluco01:gluco08))) == 8))
dat <- dat %>%
  dplyr::mutate(hb1ac_na = as.integer(rowSums(is.na(dplyr::pick(hb1ac01:hb1ac08))) == 8))
dat <- dat %>%
  dplyr::mutate(egfr_na = as.integer(rowSums(is.na(dplyr::pick(egfr01:egfr08))) == 8))
dat <- dat %>%
  dplyr::mutate(nlr_na = as.integer(rowSums(is.na(dplyr::pick(nlr01:nlr08))) == 8))
dat <- dat %>%
  dplyr::mutate(plat_na = as.integer(rowSums(is.na(dplyr::pick(plat01:plat08))) == 8))
dat <- dat %>%
  dplyr::mutate(drugs_na = as.integer(rowSums(is.na(dplyr::pick(f_hta_01:f_hta_08))) == 8))


dat$bmi_ok<-with(dat,ifelse(!is.na(bmi00) & bmi_na==0,1,0))
dat$wc_ok<-with(dat,ifelse(!is.na(wc00) & wc_na==0,1,0))
dat$sbp_ok<-with(dat,ifelse(!is.na(sbp00) & bp_na==0,1,0))
dat$dbp_ok<-with(dat,ifelse(!is.na(dbp00) & bp_na==0,1,0))
dat$lipids_ok<-with(dat,ifelse(!is.na(ldlc_hdlc00) & lipids_na==0,1,0))
dat$gluco_ok<-with(dat,ifelse(!is.na(gluco00) & gluco_na==0,1,0))
dat$hb1ac_ok<-with(dat,ifelse(!is.na(hb1ac00) & hb1ac_na==0,1,0))
dat$egfr_ok<-with(dat,ifelse(!is.na(egfr00) & egfr_na==0,1,0))
dat$nlr_ok<-with(dat,ifelse(!is.na(nlr00) & nlr_na==0,1,0))
dat$plat_ok<-with(dat,ifelse(!is.na(plat00) & plat_na==0,1,0))
dat$drugs_ok<-with(dat,ifelse(!is.na(f_hta_00) & drugs_na==0,1,0))


dim(dat)[1] #5399

length(which(is.na(dat$bmi00))) #0, Everyone has BMI at baseline
length(which(dat$bmi_na==1)) #-126, we remove 126 participants with BMI values only at baseline
length(which(dat$bmi_ok==1)) #n = 5273 for BMI analyses

length(which(is.na(dat$wc00))) #0, Everyone has WC at baseline
length(which(dat$wc_na==1)) #-459, we remove 459 participants with WC values only at baseline
length(which(dat$wc_ok==1)) #n = 4940 for WC / WHtR analyses

length(which(is.na(dat$sbp00))) #-14, we remove 14 participants without sbp values at baseline
length(which(!is.na(dat$sbp00) & dat$bp_na==1)) #-131, we remove 159 participants with sbp values only at baseline
length(which(dat$sbp_ok==1)) #n = 5254 for sbp analyses

length(which(is.na(dat$dbp00))) #-14, we remove 14 participants without dbp values at baseline
length(which(!is.na(dat$dbp00) & dat$bp_na==1)) #-131, we remove 131 participants with dbp values only at baseline
length(which(dat$dbp_ok==1)) #n = 5254 for dbp analyses

length(which(is.na(dat$ldlc_hdlc00))) #-392, we remove 392 participants without lipid profile values at baseline
length(which(!is.na(dat$ldlc_hdlc00) & dat$lipids_na==1)) #-727, we remove 727 participants with lipid profile values only at baseline
length(which(dat$lipids_ok==1)) #n = 4280 for lipid profile analyses

length(which(is.na(dat$gluco00))) #-383, we remove 383 participants without glucose values at baseline
length(which(!is.na(dat$gluco00) & dat$gluco_na==1)) #-638, we remove 638 participants with glucose values only at baseline
length(which(dat$gluco_ok==1)) #n = 4378 for glucose analyses

length(which(is.na(dat$hb1ac00))) #-3933, we remove 3933 participants without hb1ac values at baseline
length(which(!is.na(dat$hb1ac00) & dat$hb1ac_na==1)) #-228, we remove 224 participants with hb1ac values only at baseline
length(which(dat$hb1ac_ok==1)) #n = 1238 for hb1ac analyses

length(which(is.na(dat$egfr00))) #-1637, we remove 1637 participants without egfr values at baseline
length(which(!is.na(dat$egfr00) & dat$egfr_na==1)) #-463, we remove 463 participants with egfr values only at baseline
length(which(dat$egfr_ok==1)) #n = 3299 for egfr analyses

length(which(is.na(dat$nlr00))) #-3277, we remove 3277 participants without nlr values at baseline
length(which(!is.na(dat$nlr00) & dat$nlr_na==1)) #-544, we remove 544 participants with nlr values only at baseline
length(which(dat$nlr_ok==1)) #n = 1578 for nlr analyses

length(which(is.na(dat$plat00))) #-2159, we remove 2159 participants without platelet values at baseline
length(which(!is.na(dat$plat00) & dat$plat_na==1)) #-613, we remove 613 participants with platelet values only at baseline
length(which(dat$plat_ok==1)) #n = 2627 for plat analyses

length(which(dat$drugs_ok==1)) #n = 5399 for drug use analyses (all participants have info)


# PREPARATION OF DATABASE FOR SURVIVAL ANALYSES #

vars01<-c("seg00","seg01","seg02","seg03","seg04","seg05","seg06","seg07","seg08")
vars02<-c("toseg00","toseg01","toseg02","toseg03","toseg04","toseg05","toseg06","toseg07","toseg08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-as.numeric(dat[,vars01[i]]-dat$seg00)
}


# RECODIFICATION TO CATEGORICAL VARIABLES #

vars01<-c("bmi00","bmi01","bmi02","bmi03","bmi04","bmi05","bmi06","bmi07","bmi08")
vars02<-c("obesity_00","obesity_01","obesity_02","obesity_03","obesity_04","obesity_05","obesity_06","obesity_07","obesity_08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]>=30,1,0))
}

vars01<-c("wc00","wc01","wc02","wc03","wc04","wc05","wc06","wc07","wc08")
vars02<-c("adobesity_00","adobesity_01","adobesity_02","adobesity_03","adobesity_04","adobesity_05","adobesity_06","adobesity_07","adobesity_08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]<103 & sexo==0,0,
                                   ifelse(dat[,vars01[i]]>=103 & sexo==0,1,
                                          ifelse(dat[,vars01[i]]<89 & sexo==1,0,
                                                 ifelse(dat[,vars01[i]]>=89 & sexo==1,1,NA)))))
}

# High central adiposity (>=0.6): https://www.nice.org.uk/guidance/ng246/chapter/Identifying-and-assessing-overweight-obesity-and-central-adiposity

vars01<-c("whtr00","whtr01","whtr02","whtr03","whtr04","whtr05","whtr06","whtr07","whtr08")
vars02<-c("c_adip_00","c_adip_01","c_adip_02","c_adip_03","c_adip_04","c_adip_05","c_adip_06","c_adip_07","c_adip_08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]>=0.6,1,0))
}

vars01<-c("sbp00","sbp01","sbp02","sbp03","sbp04","sbp05","sbp06","sbp07","sbp08")
vars02<-c("dbp00","dbp01","dbp02","dbp03","dbp04","dbp05","dbp06","dbp07","dbp08")
vars03<-c("bp_hi_00","bp_hi_01","bp_hi_02","bp_hi_03","bp_hi_04","bp_hi_05","bp_hi_06","bp_hi_07","bp_hi_08")

for(i in 1:length(vars01))
{
  dat[,vars03[i]]<-with(dat,ifelse(dat[,vars01[i]]>=140 & dat[,vars02[i]]>=90,1,
                                   ifelse(dat[,vars01[i]]>=140 & dat[,vars02[i]]<90,1,
                                          ifelse(dat[,vars01[i]]<140 & dat[,vars02[i]]>=90,1,
                                                 ifelse(dat[,vars01[i]]<140 & dat[,vars02[i]]<90,0,NA)))))
}

# High pulse pressure >=60 mmHg: https://pubmed.ncbi.nlm.nih.gov/29226693/

vars01<-c("pp00","pp01","pp02","pp03","pp04","pp05","pp06","pp07","pp08")
vars02<-c("pp_hi_00","pp_hi_01","pp_hi_02","pp_hi_03","pp_hi_04","pp_hi_05","pp_hi_06","pp_hi_07","pp_hi_08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]>=60,1,0))
}

vars01<-c("tg00","tg01","tg02","tg03","tg04","tg05","tg06","tg07","tg08")
vars02<-c("tg_hi150_00","tg_hi150_01","tg_hi150_02","tg_hi150_03","tg_hi150_04","tg_hi150_05","tg_hi150_06","tg_hi150_07","tg_hi150_08")
vars03<-c("tg_hi200_00","tg_hi200_01","tg_hi200_02","tg_hi200_03","tg_hi200_04","tg_hi200_05","tg_hi200_06","tg_hi200_07","tg_hi200_08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]>=150,1,0))
  dat[,vars03[i]]<-with(dat,ifelse(dat[,vars01[i]]>=200,1,0))
}

# Elevated LDL-C: >=130 mg/dL is the most essential definition for high CV risk individuals (https://jamanetwork.com/journals/jama/article-abstract/193847)

vars01<-c("ldlc00","ldlc01","ldlc02","ldlc03","ldlc04","ldlc05","ldlc06","ldlc07","ldlc08")
vars02<-c("ldl_hi100_00","ldl_hi100_01","ldl_hi100_02","ldl_hi100_03","ldl_hi100_04","ldl_hi100_05","ldl_hi100_06","ldl_hi100_07","ldl_hi100_08")
vars03<-c("ldl_hi130_00","ldl_hi130_01","ldl_hi130_02","ldl_hi130_03","ldl_hi130_04","ldl_hi130_05","ldl_hi130_06","ldl_hi130_07","ldl_hi130_08")
vars04<-c("ldl_hi160_00","ldl_hi160_01","ldl_hi160_02","ldl_hi160_03","ldl_hi160_04","ldl_hi160_05","ldl_hi160_06","ldl_hi160_07","ldl_hi160_08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]>=100,1,0))
  dat[,vars03[i]]<-with(dat,ifelse(dat[,vars01[i]]>=130,1,0))
  dat[,vars04[i]]<-with(dat,ifelse(dat[,vars01[i]]>=160,1,0))
}

# High LDL-C/HDL-C: >=3 men, >=2.5 women (https://pmc.ncbi.nlm.nih.gov/articles/PMC2747394/)

vars01<-c("ldlc_hdlc00","ldlc_hdlc01","ldlc_hdlc02","ldlc_hdlc03","ldlc_hdlc04","ldlc_hdlc05","ldlc_hdlc06","ldlc_hdlc07","ldlc_hdlc08")
vars02<-c("ldl_hdl_hi_00","ldl_hdl_hi_01","ldl_hdl_hi_02","ldl_hdl_hi_03","ldl_hdl_hi_04","ldl_hdl_hi_05","ldl_hdl_hi_06","ldl_hdl_hi_07","ldl_hdl_hi_08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]>=3 & sexo==0,1,
                                   ifelse(dat[,vars01[i]]<3 & sexo==0,0,
                                          ifelse(dat[,vars01[i]]>=2.5 & sexo==1,1,
                                                 ifelse(dat[,vars01[i]]<2.5 & sexo==1,0,NA)))))
}

vars01<-c("hdlc00","hdlc01","hdlc02","hdlc03","hdlc04","hdlc05","hdlc06","hdlc07","hdlc08")
vars02<-c("hdl_lo_00","hdl_lo_01","hdl_lo_02","hdl_lo_03","hdl_lo_04","hdl_lo_05","hdl_lo_06","hdl_lo_07","hdl_lo_08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]<40 & sexo==0,1,
                                   ifelse(dat[,vars01[i]]>=40 & sexo==0,0,
                                          ifelse(dat[,vars01[i]]<50 & sexo==1,1,
                                                 ifelse(dat[,vars01[i]]>=50 & sexo==1,0,NA)))))
}

# Impaired fasting glucose is >= 100 mg/dL (https://diabetesjournals.org/care/article/49/Supplement_1/S27/163926/2-Diagnosis-and-Classification-of-Diabetes)

vars01<-c("gluco00","gluco01","gluco02","gluco03","gluco04","gluco05","gluco06","gluco07","gluco08")
vars02<-c("gluco_hi100_00","gluco_hi100_01","gluco_hi100_02","gluco_hi100_03","gluco_hi100_04","gluco_hi100_05","gluco_hi100_06","gluco_hi100_07","gluco_hi100_08")
vars03<-c("gluco_hi110_00","gluco_hi110_01","gluco_hi110_02","gluco_hi110_03","gluco_hi110_04","gluco_hi110_05","gluco_hi110_06","gluco_hi110_07","gluco_hi110_08")
vars04<-c("gluco_hi126_00","gluco_hi126_01","gluco_hi126_02","gluco_hi126_03","gluco_hi126_04","gluco_hi126_05","gluco_hi126_06","gluco_hi126_07","gluco_hi126_08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]>=100,1,0))
  dat[,vars03[i]]<-with(dat,ifelse(dat[,vars01[i]]>=110,1,0))
  dat[,vars04[i]]<-with(dat,ifelse(dat[,vars01[i]]>=126,1,0))
}

# Hb1Ac: >=6.5 as criterion for T2DM https://pubmed.ncbi.nlm.nih.gov/39651986/

vars01<-c("hb1ac00","hb1ac01","hb1ac02","hb1ac03","hb1ac04","hb1ac05","hb1ac06","hb1ac07","hb1ac08")
vars02<-c("hb1ac_hi_00","hb1ac_hi_01","hb1ac_hi_02","hb1ac_hi_03","hb1ac_hi_04","hb1ac_hi_05","hb1ac_hi_06","hb1ac_hi_07","hb1ac_hi_08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]>=6.5,1,0))
}

# CKD as egfr <60: https://pubmed.ncbi.nlm.nih.gov/38490803/

vars01<-c("egfr00","egfr01","egfr02","egfr03","egfr04","egfr05","egfr06","egfr07","egfr08")
vars02<-c("ckd_00","ckd_01","ckd_02","ckd_03","ckd_04","ckd_05","ckd_06","ckd_07","ckd_08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]<60,1,0))
}

# NLR >=2.15: high NLR is a CVD (https://pubmed.ncbi.nlm.nih.gov/24681815/) and cancer risk factor (https://pubmed.ncbi.nlm.nih.gov/24875653/)

vars01<-c("nlr00","nlr01","nlr02","nlr03","nlr04","nlr05","nlr06","nlr07","nlr08")
vars02<-c("nlr_hi_00","nlr_hi_01","nlr_hi_02","nlr_hi_03","nlr_hi_04","nlr_hi_05","nlr_hi_06","nlr_hi_07","nlr_hi_08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]>=2.15,1,0))
}

# Thrombocytosis and thrombocytopenia: https://pubmed.ncbi.nlm.nih.gov/23382888/

vars01<-c("plat00","plat01","plat02","plat03","plat04","plat05","plat06","plat07","plat08")
vars02<-c("plat_lo_00","plat_lo_01","plat_lo_02","plat_lo_03","plat_lo_04","plat_lo_05","plat_lo_06","plat_lo_07","plat_lo_08")
vars03<-c("plat_hi_00","plat_hi_01","plat_hi_02","plat_hi_03","plat_hi_04","plat_hi_05","plat_hi_06","plat_hi_07","plat_hi_08")

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]<122 & sexo==0,1,
                                   ifelse(dat[,vars01[i]]>=122 & sexo==0,0,
                                          ifelse(dat[,vars01[i]]<140 & sexo==1,1,
                                                 ifelse(dat[,vars01[i]]>=140 & sexo==1,0,NA)))))
  dat[,vars03[i]]<-with(dat,ifelse(dat[,vars01[i]]>350 & sexo==0,1,
                                   ifelse(dat[,vars01[i]]<=350 & sexo==0,0,
                                          ifelse(dat[,vars01[i]]>379 & sexo==1,1,
                                                 ifelse(dat[,vars01[i]]<=379 & sexo==1,0,NA)))))
  dat[which(dat[[vars03[i]]] == 1), vars02[i]] <- NA
  dat[which(dat[[vars02[i]]] == 1), vars03[i]] <- NA
}


dat$obesity_inicio<-dat$obesity_00
dat$obesity_seg<-rowSums(!is.na(dat[,grep("obesity_0", names(dat))]))
dat$obesity_any<-as.integer(apply(dat[,grep("obesity_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$adobesity_inicio<-dat$adobesity_00
dat$adobesity_seg<-rowSums(!is.na(dat[,grep("adobesity_0", names(dat))]))
dat$adobesity_any<-as.integer(apply(dat[,grep("adobesity_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$c_adip_inicio<-dat$c_adip_00
dat$c_adip_seg<-rowSums(!is.na(dat[,grep("c_adip_0", names(dat))]))
dat$c_adip_any<-as.integer(apply(dat[,grep("c_adip_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$bp_hi_inicio<-dat$bp_hi_00
dat$bp_hi_seg<-rowSums(!is.na(dat[,grep("bp_hi_0", names(dat))]))
dat$bp_hi_any<-as.integer(apply(dat[,grep("bp_hi_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$pp_hi_inicio<-dat$pp_hi_00
dat$pp_hi_seg<-rowSums(!is.na(dat[,grep("pp_hi_0", names(dat))]))
dat$pp_hi_any<-as.integer(apply(dat[,grep("pp_hi_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$tg_hi150_inicio<-dat$tg_hi150_00
dat$tg_hi150_seg<-rowSums(!is.na(dat[,grep("tg_hi150_0", names(dat))]))
dat$tg_hi150_any<-as.integer(apply(dat[,grep("tg_hi150_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$tg_hi200_inicio<-dat$tg_hi200_00
dat$tg_hi200_seg<-rowSums(!is.na(dat[,grep("tg_hi200_0", names(dat))]))
dat$tg_hi200_any<-as.integer(apply(dat[,grep("tg_hi200_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$ldl_hi100_inicio<-dat$ldl_hi100_00
dat$ldl_hi100_seg<-rowSums(!is.na(dat[,grep("ldl_hi100_0", names(dat))]))
dat$ldl_hi100_any<-as.integer(apply(dat[,grep("ldl_hi100_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$ldl_hi130_inicio<-dat$ldl_hi130_00
dat$ldl_hi130_seg<-rowSums(!is.na(dat[,grep("ldl_hi130_0", names(dat))]))
dat$ldl_hi130_any<-as.integer(apply(dat[,grep("ldl_hi130_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$ldl_hi160_inicio<-dat$ldl_hi160_00
dat$ldl_hi160_seg<-rowSums(!is.na(dat[,grep("ldl_hi160_0", names(dat))]))
dat$ldl_hi160_any<-as.integer(apply(dat[,grep("ldl_hi160_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$ldl_hdl_hi_inicio<-dat$ldl_hdl_hi_00
dat$ldl_hdl_hi_seg<-rowSums(!is.na(dat[,grep("ldl_hdl_hi_0", names(dat))]))
dat$ldl_hdl_hi_any<-as.integer(apply(dat[,grep("ldl_hdl_hi_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$hdl_lo_inicio<-dat$hdl_lo_00
dat$hdl_lo_seg<-rowSums(!is.na(dat[,grep("hdl_lo_0", names(dat))]))
dat$hdl_lo_any<-as.integer(apply(dat[,grep("hdl_lo_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$gluco_hi100_inicio<-dat$gluco_hi100_00
dat$gluco_hi100_seg<-rowSums(!is.na(dat[,grep("gluco_hi100_0", names(dat))]))
dat$gluco_hi100_any<-as.integer(apply(dat[,grep("gluco_hi100_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$gluco_hi110_inicio<-dat$gluco_hi110_00
dat$gluco_hi110_seg<-rowSums(!is.na(dat[,grep("gluco_hi110_0", names(dat))]))
dat$gluco_hi110_any<-as.integer(apply(dat[,grep("gluco_hi110_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$gluco_hi126_inicio<-dat$gluco_hi126_00
dat$gluco_hi126_seg<-rowSums(!is.na(dat[,grep("gluco_hi126_0", names(dat))]))
dat$gluco_hi126_any<-as.integer(apply(dat[,grep("gluco_hi126_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$hb1ac_hi_inicio<-dat$hb1ac_hi_00
dat$hb1ac_hi_seg<-rowSums(!is.na(dat[,grep("hb1ac_hi_0", names(dat))]))
dat$hb1ac_hi_any<-as.integer(apply(dat[,grep("hb1ac_hi_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$ckd_inicio<-dat$ckd_00
dat$ckd_seg<-rowSums(!is.na(dat[,grep("ckd_0", names(dat))]))
dat$ckd_any<-as.integer(apply(dat[,grep("ckd_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$nlr_hi_inicio<-dat$nlr_hi_00
dat$nlr_hi_seg<-rowSums(!is.na(dat[,grep("nlr_hi_0", names(dat))]))
dat$nlr_hi_any<-as.integer(apply(dat[,grep("nlr_hi_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$plat_lo_inicio<-dat$plat_lo_00
dat$plat_lo_seg<-rowSums(!is.na(dat[,grep("plat_lo_0", names(dat))]))
dat$plat_lo_any<-as.integer(apply(dat[,grep("plat_lo_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$plat_hi_inicio<-dat$plat_hi_00
dat$plat_hi_seg<-rowSums(!is.na(dat[,grep("plat_hi_0", names(dat))]))
dat$plat_hi_any<-as.integer(apply(dat[,grep("plat_hi_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))

dat$f_hta_inicio<-dat$f_hta_00
dat$f_hta_seg<-rowSums(!is.na(dat[,grep("f_hta_0", names(dat))]))
dat$f_hta_any<-as.integer(apply(dat[,grep("f_hta_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$f_chol_inicio<-dat$f_chol_00
dat$f_chol_seg<-rowSums(!is.na(dat[,grep("f_chol_0", names(dat))]))
dat$f_chol_any<-as.integer(apply(dat[,grep("f_chol_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$f_tg_inicio<-dat$f_tg_00
dat$f_tg_seg<-rowSums(!is.na(dat[,grep("f_tg_0", names(dat))]))
dat$f_tg_any<-as.integer(apply(dat[,grep("f_tg_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))
dat$f_gluco_inicio<-dat$f_gluco_00
dat$f_gluco_seg<-rowSums(!is.na(dat[,grep("f_gluco_0", names(dat))]))
dat$f_gluco_any<-as.integer(apply(dat[,grep("f_gluco_0", names(dat))], 1, function(x) any(x == 1, na.rm = TRUE)))


# Definir función "crear_debut"

crear_debut <- function(data, condicion, nueva_variable = paste0(condicion, "_d")) {
  patron <- paste0("^", condicion, "_[0-9]{2}$")
  variables <- grep(
    patron,
    names(data),
    value = TRUE)
  
  if (length(variables) == 0) {
    stop("No se han encontrado variables con el patrón ",condicion, "_00, ", condicion, "_01, etc.")}
  
  seguimientos <- as.integer(sub(paste0("^", condicion, "_"),"",variables))
  
  orden <- order(seguimientos)
  variables <- variables[orden]
  seguimientos <- seguimientos[orden]
  
  if (!0 %in% seguimientos) {
    stop("No se ha encontrado la variable basal ",condicion, "_00.")}
  
  posicion_basal <- which(seguimientos == 0)
  
  data[[nueva_variable]] <- apply(
    data[, variables, drop = FALSE],1,
    function(x) {
      if (is.na(x[posicion_basal]) || x[posicion_basal] != 0) {
        return(NA_integer_)}
      
      posiciones_debut <- which(x == 1 & seguimientos > 0)
      
      if (length(posiciones_debut) == 0) {return(NA_integer_)}
      
      seguimientos[posiciones_debut[1]]})
  data
}

dat <- crear_debut(dat, "obesity")
dat <- crear_debut(dat, "adobesity")
dat <- crear_debut(dat, "c_adip")
dat <- crear_debut(dat, "bp_hi")
dat <- crear_debut(dat, "pp_hi")
dat <- crear_debut(dat, "f_hta")
dat <- crear_debut(dat, "ldl_hi100")
dat <- crear_debut(dat, "ldl_hi130")
dat <- crear_debut(dat, "ldl_hi160")
dat <- crear_debut(dat, "ldl_hdl_hi")
dat <- crear_debut(dat, "hdl_lo")
dat <- crear_debut(dat, "tg_hi150")
dat <- crear_debut(dat, "tg_hi200")
dat <- crear_debut(dat, "f_chol")
dat <- crear_debut(dat, "f_tg")
dat <- crear_debut(dat, "gluco_hi100")
dat <- crear_debut(dat, "gluco_hi110")
dat <- crear_debut(dat, "gluco_hi126")
dat <- crear_debut(dat, "hb1ac_hi")
dat <- crear_debut(dat, "f_gluco")
dat <- crear_debut(dat, "nlr_hi")
dat <- crear_debut(dat, "plat_hi")
dat <- crear_debut(dat, "plat_lo")


# Debut clasico de CKD 

x<-with(dat,cbind(id,ckd_00,ckd_01,ckd_02,ckd_03,ckd_04,ckd_05,ckd_06,ckd_07,ckd_08))
write.table(x,"./Data/ckd.csv",sep=";")
ckd<-read.csv2("./Data/ckd_revisado.csv",header=TRUE,sep=";",dec=".")
dat<-merge2(dat,ckd,by.id=c("id"),all.x=TRUE,sort=FALSE)
ckd<-NULL
x<-NULL


vars01<-c("obesity_d","adobesity_d","c_adip_d","bp_hi_d","pp_hi_d","f_hta_d","ldl_hi100_d","ldl_hi130_d","ldl_hi160_d","ldl_hdl_hi_d","hdl_lo_d","f_chol_d",
          "tg_hi150_d","tg_hi200_d","f_tg_d","gluco_hi100_d","gluco_hi110_d","gluco_hi126_d","hb1ac_hi_d","f_gluco_d","ckd_d","nlr_hi_d","plat_lo_d","plat_hi_d")

for(i in 1:length(vars01))
  
{
  dat[,vars01[i]]<-as.numeric(dat[,vars01[i]])
  dat[,vars01[i]]<-with(dat,ifelse(is.na(dat[,vars01[i]]),0,dat[,vars01[i]]))
}

dat$okseg01<-with(dat,ifelse(is.na(toseg01),0,1))
dat$okseg02<-with(dat,ifelse(is.na(toseg02),0,1))
dat$okseg03<-with(dat,ifelse(is.na(toseg03),0,1))
dat$okseg04<-with(dat,ifelse(is.na(toseg04),0,1))
dat$okseg05<-with(dat,ifelse(is.na(toseg05),0,1))
dat$okseg06<-with(dat,ifelse(is.na(toseg06),0,1))
dat$okseg07<-with(dat,ifelse(is.na(toseg07),0,1))
dat$okseg08<-with(dat,ifelse(is.na(toseg08),0,1))

dat$okseg01_left<-with(dat,ifelse(okseg01==1,0,NA))
dat$okseg02_left<-with(dat,ifelse((okseg02==1 & okseg01==1),1,
                                  ifelse((okseg02==1 & okseg01==0),0,NA)))
dat$okseg03_left<-with(dat,ifelse((okseg03==1 & okseg02==1),2,
                                  ifelse((okseg03==1 & okseg02==0 & okseg01==1),1,
                                         ifelse((okseg03==1 & okseg02==0 & okseg01==0),0,NA))))
dat$okseg04_left<-with(dat,ifelse((okseg04==1 & okseg03==1),3,
                                  ifelse((okseg04==1 & okseg03==0 & okseg02==1),2,
                                         ifelse((okseg04==1 & okseg03==0 & okseg02==0 & okseg01==1),1,
                                                ifelse((okseg04==1 & okseg03==0 & okseg02==0 & okseg01==0),0,NA)))))
dat$okseg05_left<-with(dat,ifelse((okseg05==1 & okseg04==1),4,
                                  ifelse((okseg05==1 & okseg04==0 & okseg03==1),3,
                                         ifelse((okseg05==1 & okseg04==0 & okseg03==0 & okseg02==1),2,
                                                ifelse((okseg05==1 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==1),1,
                                                       ifelse((okseg05==1 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==0),0,NA))))))
dat$okseg06_left<-with(dat,ifelse((okseg06==1 & okseg05==1),5,
                                  ifelse((okseg06==1 & okseg05==0 & okseg04==1),4,
                                         ifelse((okseg06==1 & okseg05==0 & okseg04==0 & okseg03==1),3,
                                                ifelse((okseg06==1 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==1),2,
                                                       ifelse((okseg06==1 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==1),1,
                                                              ifelse((okseg06==1 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==0),0,NA)))))))
dat$okseg07_left<-with(dat,ifelse((okseg07==1 & okseg06==1),6,
                                  ifelse((okseg07==1 & okseg06==0 & okseg05==1),5,
                                         ifelse((okseg07==1 & okseg06==0 & okseg05==0 & okseg04==1),4,
                                                ifelse((okseg07==1 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==1),3,
                                                       ifelse((okseg07==1 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==1),2,
                                                              ifelse((okseg07==1 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==1),1,
                                                                     ifelse((okseg07==1 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==0),0,NA))))))))
dat$okseg08_left<-with(dat,ifelse((okseg08==1 & okseg07==1),7,
                                  ifelse((okseg08==1 & okseg07==0 & okseg06==1),6,
                                         ifelse((okseg08==1 & okseg07==0 & okseg06==0 & okseg05==1),5,
                                                ifelse((okseg08==1 & okseg07==0 & okseg06==0 & okseg05==0 & okseg04==1),4,
                                                       ifelse((okseg08==1 & okseg07==0 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==1),3,
                                                              ifelse((okseg08==1 & okseg07==0 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==1),2,
                                                                     ifelse((okseg08==1 & okseg07==0 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==1),1,
                                                                            ifelse((okseg08==1 & okseg07==0 & okseg06==0 & okseg05==0 & okseg04==0 & okseg03==0 & okseg02==0 & okseg01==0),0,NA)))))))))

vars01<-c("f_ultcontact","f_ultcontact_bmi","f_ultcontact_wc","f_ultcontact_sbp","f_ultcontact_dbp",
          "f_ultcontact_ldlc","f_ultcontact_hdlc","f_ultcontact_tg","f_ultcontact_gluco","f_ultcontact_hb1ac",
          "f_ultcontact_egfr","f_ultcontact_nlr","f_ultcontact_plat","f_ultcontact_drugs","f_ultcontact_lipids")
vars02<-c("seg08","bmi08","wc08","sbp08","dbp08","ldlc08","hdlc08","tg08","gluco08","hb1ac08","egfr08","nlr08","plat08","f_hta_08","ldlc_hdlc08")
vars03<-c("seg07","bmi07","wc07","sbp07","dbp07","ldlc07","hdlc07","tg07","gluco07","hb1ac07","egfr07","nlr07","plat07","f_hta_07","ldlc_hdlc07")
vars04<-c("seg06","bmi06","wc06","sbp06","dbp06","ldlc06","hdlc06","tg06","gluco06","hb1ac06","egfr06","nlr06","plat06","f_hta_06","ldlc_hdlc06")
vars05<-c("seg05","bmi05","wc05","sbp05","dbp05","ldlc05","hdlc05","tg05","gluco05","hb1ac05","egfr05","nlr05","plat05","f_hta_05","ldlc_hdlc05")
vars06<-c("seg04","bmi04","wc04","sbp04","dbp04","ldlc04","hdlc04","tg04","gluco04","hb1ac04","egfr04","nlr04","plat04","f_hta_04","ldlc_hdlc04")
vars07<-c("seg03","bmi03","wc03","sbp03","dbp03","ldlc03","hdlc03","tg03","gluco03","hb1ac03","egfr03","nlr03","plat03","f_hta_03","ldlc_hdlc03")
vars08<-c("seg02","bmi02","wc02","sbp02","dbp02","ldlc02","hdlc02","tg02","gluco02","hb1ac02","egfr02","nlr02","plat02","f_hta_02","ldlc_hdlc02")
vars09<-c("seg01","bmi01","wc01","sbp01","dbp01","ldlc01","hdlc01","tg01","gluco01","hb1ac01","egfr01","nlr01","plat01","f_hta_01","ldlc_hdlc01")
date_cols<-c("seg08","seg07","seg06","seg05","seg04","seg03","seg02","seg01")

for (i in seq_along(vars01)) {
  meas_cols <- c(vars02[i], vars03[i], vars04[i], vars05[i], vars06[i], vars07[i], vars08[i], vars09[i])
  meas_mat <- as.matrix(dat[, meas_cols])
  date_mat <- as.matrix(dat[, date_cols])
  idx <- apply(meas_mat, 1, function(x) {
    w <- which(!is.na(x))
    if (length(w) == 0) NA_integer_ else w[1]   # <- FIRST, not max(w)
  })
  out <- rep(as.Date(NA), nrow(dat))
  ok  <- !is.na(idx)
  out[ok] <- as.Date(date_mat[cbind(which(ok), idx[ok])], origin = "1970-01-01")
  dat[[vars01[i]]] <- out
  dat[,vars01[i]]<-chron(as.numeric(as.Date(dat[,vars01[i]],origin="1970-01-01")),format="d/m/y")
}


vars01<-c("obesity_d","adobesity_d","c_adip_d","bp_hi_d","pp_hi_d","f_hta_d",
          "ldl_hi100_d","ldl_hi130_d","ldl_hi160_d","ldl_hdl_hi_d","hdl_lo_d","f_chol_d",
          "tg_hi150_d","tg_hi200_d","f_tg_d","gluco_hi100_d","gluco_hi110_d","gluco_hi126_d","hb1ac_hi_d","f_gluco_d",
          "ckd_d","nlr_hi_d","plat_lo_d","plat_hi_d")
vars02<-NULL
vars03<-NULL
vars04<-NULL
vars05<-NULL
vars06<-NULL
vars07<-c("f_ultcontact_bmi","f_ultcontact_wc","f_ultcontact_wc","f_ultcontact_sbp","f_ultcontact_sbp","f_ultcontact_drugs",
          "f_ultcontact_ldlc","f_ultcontact_ldlc","f_ultcontact_ldlc","f_ultcontact_lipids","f_ultcontact_hdlc","f_ultcontact_drugs",
          "f_ultcontact_tg","f_ultcontact_tg","f_ultcontact_drugs","f_ultcontact_gluco","f_ultcontact_gluco","f_ultcontact_gluco","f_ultcontact_hb1ac","f_ultcontact_drugs",
          "f_ultcontact_egfr","f_ultcontact_nlr","f_ultcontact_plat","f_ultcontact_plat")

for(i in 1:length(vars01))
  
{
  vars02<-c(vars02,paste("to",vars01[i],sep=""))
  vars03<-c(vars03,paste(vars01[i],"_left",sep=""))
  vars04<-c(vars04,paste("to",vars01[i],"_left",sep=""))
  vars05<-c(vars05,paste("to",vars01[i],"_right",sep=""))
  vars06<-c(vars06,paste(vars01[i],"_when",sep=""))
}


for(i in 1:length(vars01))
  
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]==1,toseg01,
                                   ifelse(dat[,vars01[i]]==2,toseg02,
                                          ifelse(dat[,vars01[i]]==3,toseg03,
                                                 ifelse(dat[,vars01[i]]==4,toseg04,
                                                        ifelse(dat[,vars01[i]]==5,toseg05,
                                                               ifelse(dat[,vars01[i]]==6,toseg06,
                                                                      ifelse(dat[,vars01[i]]==7,toseg07,
                                                                             ifelse(dat[,vars01[i]]==8,toseg08,dat[,vars07[i]]-seg00)))))))))
}

for(i in 1:length(vars01))
  
{
  dat[,vars03[i]]<-with(dat,ifelse(dat[,vars01[i]]==1,okseg01_left,
                                   ifelse(dat[,vars01[i]]==2,okseg02_left,
                                          ifelse(dat[,vars01[i]]==3,okseg03_left,
                                                 ifelse(dat[,vars01[i]]==4,okseg04_left,
                                                        ifelse(dat[,vars01[i]]==5,okseg05_left,
                                                               ifelse(dat[,vars01[i]]==6,okseg06_left,
                                                                      ifelse(dat[,vars01[i]]==7,okseg07_left,
                                                                             ifelse(dat[,vars01[i]]==8,okseg08_left,0)))))))))
  
  
}

for(i in 1:length(vars03))
  
{
  
  dat[,vars04[i]]<-with(dat,ifelse(dat[,vars03[i]]==0,0,
                                   ifelse(dat[,vars03[i]]==1,toseg01,
                                          ifelse(dat[,vars03[i]]==2,toseg02,
                                                 ifelse(dat[,vars03[i]]==3,toseg03,
                                                        ifelse(dat[,vars03[i]]==4,toseg04,
                                                               ifelse(dat[,vars03[i]]==5,toseg05,
                                                                      ifelse(dat[,vars03[i]]==6,toseg06,
                                                                             ifelse(dat[,vars03[i]]==7,toseg07,dat[,vars07[i]]-seg00)))))))))
}


for(i in 1:length(vars01))
  
{  
  dat[,vars05[i]]<-with(dat,ifelse(dat[,vars01[i]]==1,toseg01,
                                   ifelse(dat[,vars01[i]]==2,toseg02,
                                          ifelse(dat[,vars01[i]]==3,toseg03,
                                                 ifelse(dat[,vars01[i]]==4,toseg04,
                                                        ifelse(dat[,vars01[i]]==5,toseg05,
                                                               ifelse(dat[,vars01[i]]==6,toseg06,
                                                                      ifelse(dat[,vars01[i]]==7,toseg07,
                                                                             ifelse(dat[,vars01[i]]==8,toseg08,Inf)))))))))
  
  
}

for(i in 1:length(vars01))
  
{  
  dat[,vars06[i]]<-dat[,vars01[i]]
}

for(i in 1:length(vars01))
  
{
  dat[,vars01[i]]<-with(dat,ifelse(dat[,vars01[i]]==0,0,1))
}

# REMOVE LABELS IN ALL VARIABLS
dat[] <- lapply(dat, function(x) {
  if (inherits(x, "labelled")) {
    as.numeric(as.character(x))  # or just as.character(x), depending on your goal
  } else {
    x
  }
})

save(dat,file="./Data/LTPA_PREDIMED2.RData")


# LONG DATABASE WITH BMI DATA #

load("./Data/LTPA_PREDIMED2.RData")

dat$covar<-1
dat$bmi_basal<-dat$bmi00
dat$bmi_basal2<-dat$bmi00
dat$wc_basal<-dat$wc00
dat$whtr_basal<-dat$whtr00
dat$sbp_basal<-dat$sbp00
dat$dbp_basal<-dat$dbp00
dat$pp_basal<-dat$pp00
dat$tc_basal<-dat$tc00
dat$hdlc_basal<-dat$hdlc00
dat$ldlc_basal<-dat$ldlc00
dat$ldlc_hdlc_basal<-dat$ldlc_hdlc00
dat$tg_basal<-dat$tg00
dat$gluco_basal<-dat$gluco00
dat$hb1ac_basal<-dat$hb1ac00
dat$egfr_basal<-dat$egfr00
dat$nlr_basal<-dat$nlr00
dat$plat_basal<-dat$plat00
dat$plat_median00<-with(dat,ifelse(sexo==1 & plat00>=median(dat[dat$sexo==1,c("plat00")],na.rm=TRUE),1,
                                   ifelse(sexo==1 & plat00<median(dat[dat$sexo==1,c("plat00")],na.rm=TRUE),0,
                                          ifelse(sexo==0 & plat00>=median(dat[dat$sexo==0,c("plat00")],na.rm=TRUE),1,
                                                 ifelse(sexo==0 & plat00<median(dat[dat$sexo==0,c("plat00")],na.rm=TRUE),0,NA)))))
# plat_median: >=242 women, >=212 men

bmi_vars<-c("id","sexo","nodo","escolar00","grup_int","grup_int2","idcluster2","prop_score01","prop_score02","excl",
            "mvltpalong","mvltpa_cat2","mvltpa_cat4",
            "diabetes00","hipercol00","hipertg00","hta00","obesity00","obesity200","adobesity00","c_adip00","bmi_basal2","pp_hi_00",
            "ldl_hi130_00","ldl_hdl_hi_00","hdl_lo_00","gluco_hi100_00","gluco_hi110_00","gluco_hi126_00","ckd_00","nlr_hi_00","plat_median00",
            "f_chol_00","f_tg_00","f_gluco_00","f_hta_00","tobacco00","tobacco200","bmi_basal2","dmed00","dmedlong","kcal00","covar",
            "bmi_ok","wc_ok","sbp_ok","dbp_ok","lipids_ok","gluco_ok","hb1ac_ok","egfr_ok","nlr_ok","plat_ok",
            "bmi_basal","wc_basal","whtr_basal","sbp_basal","dbp_basal","tc_basal","hdlc_basal","ldlc_basal","ldlc_hdlc_basal","tg_basal",
            "gluco_basal","hb1ac_basal","egfr_basal","nlr_basal","plat_basal",
            "bmi00","bmi01","bmi02","bmi03","bmi04","bmi05","bmi06","bmi07","bmi08")
#setdiff(bmi_vars, names(dat))
bmi_wide<-dat[,bmi_vars]
bmi_long<-reshape(bmi_wide, 
                  varying = c("bmi00","bmi01","bmi02","bmi03","bmi04","bmi05","bmi06","bmi07","bmi08"), 
                  v.names = "bmi",
                  timevar = "seg", 
                  times = c("0","1","2","3","4","5","6","7","8"), 
                  direction = "long")

wc_vars<-c("id","wc00","wc01","wc02","wc03","wc04","wc05","wc06","wc07","wc08")
wc_wide<-dat[,wc_vars]
wc_long<-reshape(wc_wide, 
                 varying = c("wc00","wc01","wc02","wc03","wc04","wc05","wc06","wc07","wc08"), 
                 v.names = "wc",
                 timevar = "seg", 
                 times = c("0","1","2","3","4","5","6","7","8"), 
                 direction = "long")

whtr_vars<-c("id","whtr00","whtr01","whtr02","whtr03","whtr04","whtr05","whtr06","whtr07","whtr08")
whtr_wide<-dat[,whtr_vars]
whtr_long<-reshape(whtr_wide, 
                 varying = c("whtr00","whtr01","whtr02","whtr03","whtr04","whtr05","whtr06","whtr07","whtr08"), 
                 v.names = "whtr",
                 timevar = "seg", 
                 times = c("0","1","2","3","4","5","6","7","8"), 
                 direction = "long")

sbp_vars<-c("id","sbp00","sbp01","sbp02","sbp03","sbp04","sbp05","sbp06","sbp07","sbp08")
sbp_wide<-dat[,sbp_vars]
sbp_long<-reshape(sbp_wide, 
                  varying = c("sbp00","sbp01","sbp02","sbp03","sbp04","sbp05","sbp06","sbp07","sbp08"), 
                  v.names = "sbp",
                  timevar = "seg", 
                  times = c("0","1","2","3","4","5","6","7","8"), 
                  direction = "long")

dbp_vars<-c("id","dbp00","dbp01","dbp02","dbp03","dbp04","dbp05","dbp06","dbp07","dbp08")
dbp_wide<-dat[,dbp_vars]
dbp_long<-reshape(dbp_wide, 
                  varying = c("dbp00","dbp01","dbp02","dbp03","dbp04","dbp05","dbp06","dbp07","dbp08"), 
                  v.names = "dbp",
                  timevar = "seg", 
                  times = c("0","1","2","3","4","5","6","7","8"), 
                  direction = "long")

pp_vars<-c("id","pp00","pp01","pp02","pp03","pp04","pp05","pp06","pp07","pp08")
pp_wide<-dat[,pp_vars]
pp_long<-reshape(pp_wide, 
                  varying = c("pp00","pp01","pp02","pp03","pp04","pp05","pp06","pp07","pp08"), 
                  v.names = "pp",
                  timevar = "seg", 
                  times = c("0","1","2","3","4","5","6","7","8"), 
                  direction = "long")

tc_vars<-c("id","tc00","tc01","tc02","tc03","tc04","tc05","tc06","tc07","tc08")
tc_wide<-dat[,tc_vars]
tc_long<-reshape(tc_wide, 
                 varying = c("tc00","tc01","tc02","tc03","tc04","tc05","tc06","tc07","tc08"), 
                 v.names = "tc",
                 timevar = "seg", 
                 times = c("0","1","2","3","4","5","6","7","8"), 
                 direction = "long")

hdlc_vars<-c("id","hdlc00","hdlc01","hdlc02","hdlc03","hdlc04","hdlc05","hdlc06","hdlc07","hdlc08")
hdlc_wide<-dat[,hdlc_vars]
hdlc_long<-reshape(hdlc_wide, 
                   varying = c("hdlc00","hdlc01","hdlc02","hdlc03","hdlc04","hdlc05","hdlc06","hdlc07","hdlc08"), 
                   v.names = "hdlc",
                   timevar = "seg", 
                   times = c("0","1","2","3","4","5","6","7","8"), 
                   direction = "long")

ldlc_vars<-c("id","ldlc00","ldlc01","ldlc02","ldlc03","ldlc04","ldlc05","ldlc06","ldlc07","ldlc08")
ldlc_wide<-dat[,ldlc_vars]
ldlc_long<-reshape(ldlc_wide, 
                   varying = c("ldlc00","ldlc01","ldlc02","ldlc03","ldlc04","ldlc05","ldlc06","ldlc07","ldlc08"), 
                   v.names = "ldlc",
                   timevar = "seg", 
                   times = c("0","1","2","3","4","5","6","7","8"), 
                   direction = "long")

ldlc_hdlc_vars<-c("id","ldlc_hdlc00","ldlc_hdlc01","ldlc_hdlc02","ldlc_hdlc03","ldlc_hdlc04","ldlc_hdlc05","ldlc_hdlc06","ldlc_hdlc07","ldlc_hdlc08")
ldlc_hdlc_wide<-dat[,ldlc_hdlc_vars]
ldlc_hdlc_long<-reshape(ldlc_hdlc_wide, 
                        varying = c("ldlc_hdlc00","ldlc_hdlc01","ldlc_hdlc02","ldlc_hdlc03","ldlc_hdlc04","ldlc_hdlc05","ldlc_hdlc06","ldlc_hdlc07","ldlc_hdlc08"), 
                        v.names = "ldlc_hdlc",
                        timevar = "seg", 
                        times = c("0","1","2","3","4","5","6","7","8"), 
                        direction = "long")

tg_vars<-c("id","tg00","tg01","tg02","tg03","tg04","tg05","tg06","tg07","tg08")
tg_wide<-dat[,tg_vars]
tg_long<-reshape(tg_wide, 
                 varying = c("tg00","tg01","tg02","tg03","tg04","tg05","tg06","tg07","tg08"), 
                 v.names = "tg",
                 timevar = "seg", 
                 times = c("0","1","2","3","4","5","6","7","8"), 
                 direction = "long")

gluco_vars<-c("id","gluco00","gluco01","gluco02","gluco03","gluco04","gluco05","gluco06","gluco07","gluco08")
gluco_wide<-dat[,gluco_vars]
gluco_long<-reshape(gluco_wide, 
                    varying = c("gluco00","gluco01","gluco02","gluco03","gluco04","gluco05","gluco06","gluco07","gluco08"), 
                    v.names = "gluco",
                    timevar = "seg", 
                    times = c("0","1","2","3","4","5","6","7","8"), 
                    direction = "long")

hb1ac_vars<-c("id","hb1ac00","hb1ac01","hb1ac02","hb1ac03","hb1ac04","hb1ac05","hb1ac06","hb1ac07","hb1ac08")
hb1ac_wide<-dat[,hb1ac_vars]
hb1ac_long<-reshape(hb1ac_wide, 
                    varying = c("hb1ac00","hb1ac01","hb1ac02","hb1ac03","hb1ac04","hb1ac05","hb1ac06","hb1ac07","hb1ac08"), 
                    v.names = "hb1ac",
                    timevar = "seg", 
                    times = c("0","1","2","3","4","5","6","7","8"), 
                    direction = "long")

egfr_vars<-c("id","egfr00","egfr01","egfr02","egfr03","egfr04","egfr05","egfr06","egfr07","egfr08")
egfr_wide<-dat[,egfr_vars]
egfr_long<-reshape(egfr_wide, 
                    varying = c("egfr00","egfr01","egfr02","egfr03","egfr04","egfr05","egfr06","egfr07","egfr08"), 
                    v.names = "egfr",
                    timevar = "seg", 
                    times = c("0","1","2","3","4","5","6","7","8"), 
                    direction = "long")

nlr_vars<-c("id","nlr00","nlr01","nlr02","nlr03","nlr04","nlr05","nlr06","nlr07","nlr08")
nlr_wide<-dat[,nlr_vars]
nlr_long<-reshape(nlr_wide, 
                    varying = c("nlr00","nlr01","nlr02","nlr03","nlr04","nlr05","nlr06","nlr07","nlr08"), 
                    v.names = "nlr",
                    timevar = "seg", 
                    times = c("0","1","2","3","4","5","6","7","8"), 
                    direction = "long")

plat_vars<-c("id","plat00","plat01","plat02","plat03","plat04","plat05","plat06","plat07","plat08")
plat_wide<-dat[,plat_vars]
plat_long<-reshape(plat_wide, 
                    varying = c("plat00","plat01","plat02","plat03","plat04","plat05","plat06","plat07","plat08"), 
                    v.names = "plat",
                    timevar = "seg", 
                    times = c("0","1","2","3","4","5","6","7","8"), 
                    direction = "long")

age_vars<-c("id","age00","age01","age02","age03","age04","age05","age06","age07","age08")
age_wide<-dat[,age_vars]
age_long<-reshape(age_wide, 
                  varying = c("age00","age01","age02","age03","age04","age05","age06","age07","age08"), 
                  v.names = "age",
                  timevar = "seg", 
                  times = c("0","1","2","3","4","5","6","7","8"), 
                  direction = "long")

dat_long<-as.data.frame(cbind(bmi_long,wc_long[,3],whtr_long[,3],sbp_long[,3],dbp_long[,3],pp_long[,3],tc_long[,3],hdlc_long[,3],
                              ldlc_long[,3],ldlc_hdlc_long[,3],tg_long[,3],gluco_long[,3],hb1ac_long[,3],
                              egfr_long[,3],nlr_long[,3],plat_long[,3],age_long[,3]))
colnames(dat_long)<-c("id","sexo","nodo","escolar00","grup_int","grup_int2","idcluster2","prop_score01","prop_score02","excl",
                      "mvltpalong","mvltpa_cat2","mvltpa_cat4",
                      "diabetes00","hipercol00","hipertg00","hta00","obesity00","obesity200","adobesity00","c_adip00","bmi00","pp_hi_00",
                      "ldl_hi130_00","ldl_hdl_hi_00","hdl_lo_00","gluco_hi100_00","gluco_hi110_00","gluco_hi126_00","ckd_00","nlr_hi_00","plat_median00",
                      "f_chol_00","f_tg_00","f_gluco_00","f_hta_00","tobacco00","tobacco200","bmi_basal2","dmed00","dmedlong","kcal00","covar",
                      "bmi_ok","wc_ok","sbp_ok","dbp_ok","lipids_ok","gluco_ok","hb1ac_ok","egfr_ok","nlr_ok","plat_ok",
                      "bmi_basal","wc_basal","whtr_basal","sbp_basal","dbp_basal","tc_basal","hdlc_basal","ldlc_basal","ldlc_hdlc_basal","tg_basal",
                      "gluco_basal","hb1ac_basal","egfr_basal","nlr_basal","plat_basal",
                      "seg","bmi","wc","whtr","sbp","dbp","pp","tc","hdlc","ldlc","ldlc_hdlc","tg","gluco","hb1ac","egfr","nlr","plat","age")
dat_long <- dat_long %>% arrange(id, as.numeric(seg))
dat_long[c("mvltpa_cat2","mvltpa_cat4")]<-lapply(dat_long[c("mvltpa_cat2","mvltpa_cat4")],function(x) as.factor(x))

save(dat_long,file="./Data/LTPA_PREDIMED2_long.RData")
