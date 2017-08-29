## This is a library with functions for penalized single index simulations
## Author: Sergey Gitlin


require("MASS")  # for generalized inverse and mvrnorm
require("lars")
require("optimx")  # optimization wrapper package
require("expm")  # for matrix square root
require("compiler")
require("R.matlab")  # For creating .mat files to be used by matlab script
#enableJIT(3)


OLS <- function(x,y) {  # Rudimentary OLS
    out <- ginv(t(x)%*%x)%*%t(x)%*%y
}


make.g <- function(type=0,lambda=0,k=2) {
### Returns link function of the type specified
### type == -1: linear
### type == 0: Box-Cox with parameter lambda
### other types: ad-hoc functions for testing purposes. See the code.

    ## Transform index before passing it to link
    transform <- function(index) {
        index <- index/10 + 7
    }

    ## Linear without transformation (to avoid constants)
    if (type==-1) {
        g <- function(index) {
            out <- index
        }
    }

    ## Box-Cox with parameter lambda
    if (type==0) {
        g <- function(index) {
            index <- transform(index)
            if (lambda==0) {
                out <- exp(index)
            } else {
                out <- (lambda*index+1)^(1/lambda)
            }
        }
    }

    ## ~~~~~~~~~~~~~~~~~~~~~~~~~~~
    if (type==1) {
        g <- function(index) {
            out <- exp(index/k+2)+0.1*index
        }
        gin <- function(y) {
            out <- k*log(y)
        }
    }
    ## ~~~~~~~~~~~~~~~~~~~~~~~~~~~
    if (type==2) {
        g <- function(index) {
            index <- index + 1
            out <- 0.2*index + 3/(1+exp(-index*1.5))
        }
                                        #    gin <- function(y) {
                                        #        out <- -k*log(1/y-1)
                                        #    }
    }
    ## ~~~~~~~~~~~~~~~~~~~~~~~~~~~
    if (type==3) {
        k <- 3
        g <- function(index) {
            out <- index+(index/k)^3
        }
        gin <- function(y) {
            out <- k*sign(y)*((abs(y))^(1/3))
        }
    }
    ## ~~~~~~~~~~~~~~~~~~~~~~~~~~~
    if (type==4) {
        g <- function(index) {
            index <- index+1
            out <- 1.1*index + sin(index)
        }
    }
    ## ~~~~~~~~~~~~~~~~~~~~~~~~~~~
    return(g)
}




gendata <- function(seed,n,beta,rho=0.5,sigma=1,
                    regressors="normal",errors="normal",model="cont") {
    ## Set regressors to "ex1" and model to "binary"
    ## ... for an example from Fan and Li (2001)

    set.seed(seed)

    pn <- length(beta)

    ## <<< Generate data >>>

    if (regressors=="normal") {
        Sigma <- matrix(rho,nrow=pn,ncol=pn)
        diag(Sigma) <- 1
        x <- mvrnorm(n=n,mu=rep(0,times=pn),Sigma=Sigma)
    }
    if (regressors=="uniform") {  # Uniform Regressors
        x1 <- runif(n,-1,1)  # First regressor
        x2 <- matrix(runif(n*(pn-1),-1,1),nrow=n,ncol=(pn-1))  # Other regressors
        x <- cbind(x1,x2)  # All regressors
    }
    if (regressors=="exponential") {  # Exponential regressors
        x1 <- rexp(n)
        x2 <- matrix(rexp(n*(pn-1)),nrow=n,ncol=(pn-1))  # Other regressors
        x <- cbind(x1,x2)  # All regressors
    }
    if (regressors=="ex1a") {  # last two regressors Bernoulli, rest are normal
        Sigma <- matrix(nrow=pn-2,ncol=pn-2)
        for (i in 1:(pn-2)) {
            for (j in i:(pn-2)) {
                Sigma[i,j] <- rho^abs(i-j)
                Sigma[j,i] <- rho^abs(i-j)
            }
        }
        x1 <- mvrnorm(n=n,mu=rep(0,times=pn-2),Sigma=Sigma)
        x2 <- rbinom(n=n,size=1,prob=0.5)
        x3 <- rbinom(n=n,size=1,prob=0.5)
        x <- cbind(x1,x2,x3)
    }
    if (regressors=="ex1b") {  # half of regressors are binary
        Sigma <- matrix(nrow=pn,ncol=pn)
        for (i in 1:pn) {
            for (j in i:pn) {
                Sigma[i,j] <- rho^abs(i-j)
                Sigma[j,i] <- rho^abs(i-j)
            }
        }
        x <- mvrnorm(n=n,mu=rep(0,times=pn),Sigma=Sigma)
        for (k in 1:floor(length(beta)/2)) {
            x[,2*k] <- 2*(x[,2*k] > 0) - 1
        }
    }

    indextrue <- x%*%beta  # True value of index

    if (model=="binary") {  # Add extra split into logit vs probit
        l <- exp(indextrue)/(1+exp(indextrue))
        y <- rbinom(n=n,size=1,prob=l)
        u <- y - l
    } else if (model=="tobit") {
        u <- rnorm(n)
        y <- (indextrue+0.5*u) * ( (indextrue+0.5*u) > 0 )
    } else {
        ## Errors
        if (errors=="normal") {
            u <- rnorm(n)  # Normal
        }
        df <- 3
        if (errors=="chi-squared") {
            u <- (rchisq(n,df=df)-df)/(sqrt(2*df))  # Chi squared
        }
        u <- u*sigma  # scale the errors

        ## Index and dependent variable
        y <- g(indextrue) + u  # Outcomes

        ## De-mean y
        y <- y - mean(y)
    }

    list(y=y,x=x,indextrue=indextrue,u=u)

}  # End of function <<< gendata >>>


pre.ker <- function(x,type="epan") {
### ker implements Epanechnikov kernel by default and Gaussian otherwise
    sqx <- crossprod(x)
    if (type=="epan") {
        out <- (sqx<1)*0.75*(1-sqx)  # Epanechnikov kernel
    } else {
        out <- dnorm(sqx)  # Gaussian kernel
    }
}
ker <- cmpfun(pre.ker)


pre.dif <- function(x) {  # create array of Xi-Xj
    n <- dim(x)[1]
    d <- dim(x)[2]
    out <- array(dim=c(n,n,d))
    for (i in 1:n) {
        for (j in i:n) {
            out[i,j,] <- x[i,]-x[j,]
            out[j,i,] <- -out[i,j,]
        }
    }
    out
}
dif <- cmpfun(pre.dif)


scad <- function(beta,lambda,a=3.7) {  # compute SCAD penalty
    absbeta <- abs(beta)
    out <- (lambda*absbeta*(absbeta <= lambda) +
            (absbeta^2 - 2*a*lambda*absbeta + lambda^2)/(2*(1-a))
            *(lambda < absbeta)*(absbeta <= a*lambda) +
            0.5*(a+1)*lambda^2*(absbeta > a*lambda))
    sum(out)
}


MAVEobjective <- function(par,data,bandwidth,lambda,penaltytype="bridge") {
### This is the MAVE objective with the penalty term
### This version has been superceded by MAVEobjective2, which endogenously solves
### ... for the local linear parameters. This version is provided for diagnostics
### ... and experimentation only.
    ## par has the following structure:
    ## ~~~ first p-1 elements are index coefficients for 2..p covariates
    ## ~~~ next n elements are level parameters
    ## ~~~ last n elements are slope coefficients multiplying the index
    n <- length(data$y)
    par <- c(1,par)
    p <- length(par) - 2*n  # number of covariates
    beta <- par[1:p]
    a <- par[(p+1):(p+n)]
    b <- par[(p+n+1):(p+2*n)]

    indexrep <- matrix(data$x%*%beta,nrow=n,ncol=n)
    sloperep <- (indexrep - t(indexrep))*matrix(b,nrow=n,ncol=n,byrow=TRUE)
    errormatrix <- matrix(data$y,nrow=n,ncol=n) - matrix(a,nrow=n,ncol=n,byrow=TRUE) - sloperep

    kernelmatrix <- (bandwidth^p)*apply(dif(data$x)/bandwidth,c(1,2),ker)
    aux <- diag(1/colSums(kernelmatrix))
    kernelmatrix <- kernelmatrix%*%aux  # Normalize column sums to 1

    out <- sum(errormatrix^2*kernelmatrix) + penalty(penaltytype,beta,lambda)
}


kernelweights <- function(data,bandwidth,kerneltype="spherical",
                          kernelbeta=stop("Kernelbeta is required and is not supplied"),
                          HJSit=stop("HJS iteration is required and is not supplied")) {
### kernelweights returns a matrix of kernel weights with normalized column sums
### DEPENDENCIES: dif,ker
    n <- length(data$y)
    p <- dim(data$x)[2]

    ## Construct kernel weights
    if (kerneltype=="spherical") {
        kernelmatrix <- (bandwidth^p)*apply(dif(data$x)/bandwidth,c(1,2),ker)
    }
    if (kerneltype=="RMAVE") {
        ## This is RMAVE version of kernel
        indexker <- matrix(data$x%*%kernelbeta,nrow=n,ncol=n)
        deltaindexker <- indexker - t(indexker)
        kernelmatrix <- (bandwidth^p)*apply(deltaindexker/bandwidth,c(1,2),ker)
    }
    if (kerneltype=="HJS") {
        ## This is Hristache-Juditsky-Spokoiny version of kernel
        alpharho <- exp(-1/6)
        alphah <- exp(0.5/max(4,p))
        rho <- alpharho^HJSit
        bandwidth <- bandwidth*alphah^HJSit
        S <- sqrtm(diag(nrow=p) + (rho^(-2))*tcrossprod(kernelbeta))
        kernelmatrix <- (bandwidth^p)*apply(dif(data$x%*%S)/bandwidth,c(1,2),ker)
    }
    aux <- diag(1/colSums(kernelmatrix))
    kernelmatrix <- kernelmatrix%*%aux  # Normalize column sums to 1
    kernelmatrix
}


penalty <- function(type,beta,lambda) {
### DEPENDENCIES: scad
    penaltyval <- 0  # if unsupported penalty type given, no penalty will be applied
    if (type=="bridge") {
        penaltyval <- lambda*sum(sqrt(abs(beta)))  # Bridge penalty
    }
    if (type=="lasso") {
        penaltyval <- lambda*sum(abs(beta))  # LASSO penalty
    }
    if (type=="scad") {
        penaltyval <- scad(beta,lambda)  # SCAD penalty
    }
    penaltyval
}


GADEpenalty <- function(etamatrix,gamma) {
### GADEpenalty penalizes deviations from collinearity in etamatrix
### Implicitly assumes (missing) first column to be 1, so penalizes differences in rows
    out <- 0.5*gamma*sum(exp(apply(dif(etamatrix)^2,c(1,2),sum)))
}


loclinreg <- function(data,bandwidth,kerneldata=data,
                      kerneltype="spherical",kernelbeta=NA,HJSit=NA) {
### loclinreg conducts local linear regression at all points in the dataset
### WARNING: make sure to supply full data as kerneldata in single index regression
    n <- length(data$y)

    kernelmatrix <- kernelweights(kerneldata,bandwidth,kerneltype,kernelbeta,HJSit)

    xdif <- dif(data$x)

    abhat <- matrix(data=NA,nrow=n,ncol=dim(data$x)[2]+1)
    locvar <- rep(NA,times=n)
    for (i in 1:n) {
        X <- cbind(1,xdif[,i,])  # WLS regressors
        W <- diag(kernelmatrix[,i])  # WLS weights
        abhat[i,] <- ginv( t(X) %*% W %*% X ) %*% t(X) %*% W %*% data$y  # local linear fit
        locvar[i] <- sum(W %*% ((data$y-X%*%abhat[i,])^2))
    }

    list(abhat=abhat,locvar=locvar)
}


HJS <- function(data,bandwidth) {
### HJS implements simple version of HJS average derivative estimator
    n <- length(data$y)
    betahat <- colMeans(loclinreg(data,bandwidth)$abhat[,-1])
    for (k in 1:floor(2*log(n))) {
        betahat <- colMeans(loclinreg(data,bandwidth,kerneltype="HJS",
                                      kernelbeta=betahat,HJSit=k)$abhat[,-1])
    }
    betahat/betahat[1]
}


MAVEobjective2 <- function(eta,data,bandwidth,lambda,penaltytype="bridge",
                           kerneltype="spherical",kernelbeta=NA,HJSit=NA) {
### Two-stage version of the MAVE objective, with second stage solved by WLS
    beta <- c(1,eta)
    aux <- loclinreg(list(y=data$y,x=data$x%*%beta),bandwidth,data,kerneltype,kernelbeta,HJSit)

    out <- sum(aux$locvar) + penalty(penaltytype,beta,lambda)
}


GADEobjective <- function(etamatrix,data,bandwidth,lambda,gamma,penaltytype="bridge",
                          kerneltype="spherical",kernelbeta=NA,HJSit=NA) {
### Computes generalized average derivative objective: a cross between normal ADE and MAVE
    betamatrix <- cbind(1,etamatrix)
    aux <- loclinreg(list(y=data$y,x=rowSums(data$x*betamatrix)),
                     bandwidth,data,kerneltype,kernelbeta,HJSit)
    out <- sum(aux$locvar) + penalty(penaltytype,beta,lambda) + GADEpenalty(etamatrix,gamma)
}


MAVEgradient <- function(beta,data,bandwidth,lambda,penalty="bridge",
                         kerneltype="spherical",kernelbeta=NA,HJSit=NA) {
### Computes the gradient of the MAVE objective
    ## WARNING: need to decide how to represent lack of derivative at true zeros.
    ## ... This will depend on whether optimization algorithms accept occasional NAs.
    ## ... If not, we can try returning zero along relevant dimensions.
    n <- length(data$y)
    beta <- c(1,beta)
    p <- length(beta)

    ## Construct difference of indices - basic ingredient of internal optimization
    indexrep <- matrix(data$x%*%beta,nrow=n,ncol=n)
    deltaindex <- indexrep - t(indexrep)

    xdif <- dif(data$x)

    kernelmatrix <- kernelweights(data,bandwidth,kerneltype,kernelbeta,HJSit)

    cleangradient <- rep(0,p-1)
    for (j in 1:n) {  # Add up variance derivative terms at each observation j
        X <- cbind(1,deltaindex[,j])  # WLS regressors
        W <- diag(kernelmatrix[,j])  # WLS weights
        abhat <- ginv( t(X) %*% W %*% X ) %*% t(X) %*% W %*% data$y  # local linear fit
        cleangradient <- cleangradient - as.vector(2*colSums(
            as.vector(W %*% (data$y-X%*%abhat)*abhat[2])*xdif[,j,-1]))
    }

    penaltygrad <- rep(0,p-1)  # if unsupported penalty type, no penalty is applied
    if (penalty=="bridge") {
        penaltygrad <- lambda*sign(beta[-1])*(abs(beta[-1])^(-0.5))  # Bridge penalty
    }
    if (penalty=="lasso") {
        penaltygrad <- lambda*sign(beta[-1])  # LASSO penalty
    }
    if (penalty=="scad") {
        #penaltygrad <- scad(beta,lambda)  # SCAD penalty
    }

    ## This part sets derivative to 0 at true zeros. Not sure why this works, or when.
    flag <- beta[-1] == 0
    penaltygrad[flag] <- 0

    out <- cleangradient + penaltygrad
}


loclinprederr <- function(beta,trainingdata,testdata,bandwidth,
                           kerneltype="spherical",kernelbeta=NA,HJSit=NA) {
### Computes mean prediction errors given training and testing data
    data <- list(y=c(trainingdata$y,testdata$y),x=rbind(trainingdata$x,testdata$x))

    n1 <- length(trainingdata$y)
    n2 <- length(testdata$y)
    n <- length(data$y)
#    beta <- c(1,beta)
    p <- length(beta)

    ## Construct difference of indices - basic ingredient of internal optimization
    indexrep <- matrix(data$x%*%beta,nrow=n,ncol=n)
    deltaindex <- indexrep - t(indexrep)

    ## Should I normalize differently here? Seems like it doesn't matter at all.
    kernelmatrix <- kernelweights(data,bandwidth,kerneltype,kernelbeta,HJSit)

    mspe <- 0
    for (j in (n1+1):n) {  # Add up variance terms at each test observation j
        X <- cbind(1,deltaindex[(1:n1),j])  # WLS regressors
        W <- diag(kernelmatrix[(1:n1),j])  # WLS weights
        abhat <- ginv( t(X) %*% W %*% X ) %*% t(X) %*% W %*% trainingdata$y  # local linear fit
        mspe <- mspe + (testdata$y[(j-n1)]-abhat[1])^2
    }

    out <- mspe/n2
}


SCV <- function(data,index,bandwidthscale=1,nameprefix="") {
### SCV conducts Separated Crossvalidation via a call to matlab and authors' code
### DEPENDENCIES: runs on the SSCC cluster on Linux
### nameprefix allows concurrent simulations to have the same index and not clash on...
### ... mat files
    starttime <- Sys.time()  # Start the clock
    system("mkdir -p /tmp/sgz681")  # Create directory if it doesn't yet exist
    matfile <- sprintf("/tmp/sgz681/sgz681_%s_data[%08i].mat",nameprefix,index)
    writeMat(matfile,y=data$y,x=data$x,hscale=bandwidthscale)
    system(sprintf("run_mcc stdmatcode %s",matfile))
    ret <- readMat(matfile)
    file.remove(matfile)
    out <- list(nonzeros=ret$nonzeros,
                timespent=difftime(Sys.time(),starttime,units="mins"))
}


saveresults <- function(nameprefix,index,callargs,
                        truebeta,betahat,value,convcode,timespent,
                        writetxt=FALSE) {
### saveresults saves the results to standardized output files to be processed later
### WARNING: operates in the global environment, so the write path might depend on it
    filename <- sprintf("./results/%s_stdout[%08i].Rdata",nameprefix,index)
    save(callargs,truebeta,betahat,value,convcode,timespent,file=filename)
    if (writetxt) {
        filename <- sprintf("./results/%s_stdout[%08i].txt",nameprefix,index)
        writeLines("Parameters:",filename)
        sink(file=filename,append=TRUE)
        cat("n:",callargs$n,"| bandwidth:",callargs$bandwidth,
            "| lambda:",callargs$lambda,"| seed:",callargs$seed,
            "\n")
        cat("Computed coefficients:\n")
        print(betahat)
        cat("Value with penalty:",value,"\n")
        cat("Convergence code (0==convergence, 1==maxit achieved):",convcode,
            "\n")
        cat("Index:",index,"\n\n\n")
        sink()
    }
}


refinetruezeros <- function(objective,betahat) {
### refinetruezeros finds exact zeros in betahat from optimizing objective
### WARNING: take care with the environment of the objective
    ## WARNING: path-dependent, so not the 'best' or 'smallest' solution
    prevbeta <- NA
    while (!identical(betahat,prevbeta)) {
        prevbeta <- betahat
        for (i in 1:length(betahat)) {
            modbeta <- betahat
            modbeta[i] <- 0
            if (objective(modbeta) < objective(betahat)) {
                betahat <- modbeta
            }
        }
    }
    betahat
}


PenMAVE <- function(data,bandwidth,lambda,penaltytype="bridge",kerneltype="HJS",
                    startbeta=seq(0,0,length.out=dim(data$x)[2]-1),
                    method="BFGS",itnmax=200,usegradient=FALSE,checkKT=FALSE) {
### PenMAVE implements Penalized MAVE
    ## twostage: leave this at TRUE. FALSE will slow computations down dramatically.
    twostage <- TRUE  # Moved out of options to make it less accessible.

    ## Start the clock
    starttime <- Sys.time()

    n <- length(data$y)
    p <- dim(data$x)[2]

    wrapobjective <- function(par) {
        out <- MAVEobjective(par,data,bandwidth,lambda,penaltytype)
        out
    }
    wrapobjective2 <- function(beta) {
        out <- MAVEobjective2(beta,data,bandwidth,lambda,penaltytype)
        out
    }
    wrapgradient <- function(beta) {
        out <- MAVEgradient(beta,data,bandwidth,lambda,penaltytype)
        out
    }
    MAVEinnervalue <- function(beta) {  # BAD version - don't use. Serves as a check.
        wrap <- function(auxpar) {
            out <- MAVEobjective(c(beta,auxpar),data,bandwidth,lambda,penaltytype)
            out
        }
        start <- seq(0,0,length.out=2*n)
        sol <- optimx(start,wrap,method=method,itnmax=itnmax)
        out <- sol$value
        out
    }

    control <- list(trace=1,kkt=checkKT)

    if (twostage) {  # If doing two-stage optimization:
        ## Starting values for optimization
        par <- startbeta

        ## Preliminary optimization by Nelder-Mead
        if (TRUE) {
            sol <- optimx(par,wrapobjective2,method="Nelder-Mead",
                          itnmax=itnmax,control=control)
            par <- as.vector(sol[,1:(p-1)],mode="numeric")  # Solution of prelim. opt.
        }

        if (usegradient) {
            ## Intermediate optim. with analytic gradient - using optim, NOT optimx
            cat("\nStarting optimization with analytic gradient...\n")
            intcontrol <- list(trace=1,maxit=itnmax)
            sol <- optim(par,wrapobjective2,gr=wrapgradient,
                         method=method,control=intcontrol)
            par <- sol$par  # Solution of int. opt.
            cat("Obtained solution (without first coefficient):\n")
            print(par)
            parhat <- par
            convcode <- sol$convergence
            ## This is a workaround to avoid problems with the code assembling results
            ##sol <- c(sol,convcode=convcode)
        }

        if (TRUE) {
            ## Optimization without analytic gradient
            cat("\nStarting optimization with spherical kernel and no analytic derivative...\n")
            sol <- optimx(par,wrapobjective2,method=method,itnmax=itnmax,control=control)
            parhat <- as.vector(sol[,1:(p-1)],mode="numeric")
            convcode <- sol$convcode
        }

        if ((kerneltype=="RMAVE")|(kerneltype=="HJS")) {
            ## Implements RMAVE/HJS - that is, uses estimated beta to refine kernel
            for (k in 1:floor(2*log(n))) {
                cat("\nStarting round",k,"of kernel refinement procedure...\n")
                wrapobjective2 <- function(beta) {
                    out <- MAVEobjective2(beta,data,bandwidth,lambda,penaltytype,kerneltype,c(1,parhat),HJSit=k)
                    out
                }
                sol <- optimx(parhat,wrapobjective2,method=method,itnmax=itnmax,control=control)
                parhat <- as.vector(sol[,1:(p-1)],mode="numeric")
            }
            convcode <- sol$convcode
        }

        ## Iteratively find exact zeros from optimization
        betahat <- refinetruezeros(wrapobjective2,as.matrix(parhat))
        value <- wrapobjective2(betahat)
        betahat <- c(1,as.vector(betahat))

    } else {  # This option is inferior and will not be supported
        ## If optimizing everything at the same time:
        n <- length(data$y)
        p <- length(startbeta)+1
        par <- seq(0,0,length.out=2*n+p-1)
        sol <- optimx(par,wrapobjective,method=method,itnmax=itnmax,control=control)
        parhat <- sol[,1:(2*n+p-1)]  # full set of fitted parameters, w/o the first one
    }

    list(betahat=betahat,value=value,convcode=convcode,
         timespent=difftime(Sys.time(),starttime,units="mins"))
}
#PenMAVE <- cmpfun(pre.PenMAVE)


tryMAVE <- function(n,bandwidth,lambda,model="ex2a10",
                        penaltytype="bridge",kerneltype="HJS",
                        method="BFGS",itnmax=200,usegradient=FALSE,checkKT=FALSE,
                        seed=1,index=0,nameprefix="",writetxt=FALSE) {
### WARNING: do not specify vector values for method; currently not supported.
    callargs <- mget(ls())  # Get all objects in the environment
### INPUTS:
    ## kerneltype: SCV for Separated Crossvalidation, or one of (spherical,HJS,RMAVE)
### OUTPUT: files indexed by 'index' in format [%08i]

    if (model=="ex1a") {
        truebeta <- c(3,1.5,0,0,2,0,0,0)
        data <- gendata(seed,n,truebeta,regressors="ex1a",model="binary")
    }
    if (model=="ex1b") {
        truebeta <- c(3,1.5,0,0,2,0,0,0)
        data <- gendata(seed,n,truebeta,regressors="ex1b",model="binary")
    }
    if (model=="ex2a5") {
        truebeta <- rep(0,times=20)
        truebeta[1:5] <- 1
        data <- gendata(seed,n,truebeta,rho=0,regressors="normal",model="tobit")
    }
    if (model=="ex2a10") {
        truebeta <- rep(0,times=20)
        truebeta[1:10] <- 1
        data <- gendata(seed,n,truebeta,rho=0,regressors="normal",model="tobit")
    }
    if (model=="ex2b5") {
        truebeta <- rep(0,times=20)
        truebeta[1:5] <- 1
        data <- gendata(seed,n,truebeta,regressors="ex1b",model="tobit")
    }
    if (model=="ex2b10") {
        truebeta <- rep(0,times=20)
        truebeta[1:10] <- 1
        data <- gendata(seed,n,truebeta,regressors="ex1b",model="tobit")
    }
    if ((model=="ozone")|(model=="ozone2")) {
        set.seed(seed)
        truebeta <- rep(0,times=9)
        truebeta[1] <- 1
        require(lattice)
        y <- environmental$ozone
        y <- (y-mean(y))/sd(y)
        r <- environmental$radiation
        t <- environmental$temperature
        w <- environmental$wind
        if (model=="ozone") {
            x <- cbind(r,t,w,r^2,r*t,r*w,t^2,t*w,w^2)
        } else {
            x <- cbind(w,r,t,r^2,r*t,r*w,t^2,t*w,w^2)
        }
        x <- x - matrix(colMeans(x),nrow=dim(x)[1],ncol=dim(x)[2],byrow=TRUE)
        x <- x%*%diag(sqrt(diag(var(x)))^(-1))
        trainingset <- sample(length(y),56)
        data <- list(y=y[trainingset],x=x[trainingset,])
        testdata <- list(y=y[-trainingset],x=x[-trainingset,])
    }


    if (kerneltype=="SCV") {  # Do separated crossvalidation via a call to matlab
        ## WARNING: bandwidth here denotes bandwidth scaling relative to the...
        ## ... rule-of-thumb used in SCV code
        aux <- SCV(data,index,bandwidth,nameprefix)
        p <- dim(data$x)[2]
        betahat <- rep(0,times=p)
        betahat[aux$nonzeros] <- 1
        value <- convcode <- 0
        timespent <- aux$timespent
    } else {  # Do PenMAVE
        aux <- PenMAVE(data,bandwidth,lambda,penaltytype,kerneltype,HJS(data,bandwidth)[-1],
                       method=method,itnmax=itnmax,usegradient=usegradient,checkKT=checkKT)
        betahat <- aux$betahat
        value <- aux$value
        convcode <- aux$convcode
        timespent <- aux$timespent

        if ((model=="ozone")|(model=="ozone2")) {
            mspe <- loclinprederr(betahat,data,testdata,bandwidth,kerneltype=kerneltype,
                                  kernelbeta=betahat,HJSit=floor(2*log(n)))
            value <- mspe  ## TEMPORARY - to avoid modifying assemble.R
        }
    }

    ## Report results to standard output
    cat("Call arguments:\n")
    print(callargs)
    cat("Value with penalty (at refined coefficient values):\n")
    print(value)
    cat("Convergence code. 0==convergence, 1==maxit achieved.\n")
    print(convcode)
    cat("Time spent:",timespent,"mins\n")
    cat("Coefficients (refined to get some true zeros):\n")
    print(betahat)

    ## Save results
    saveresults(nameprefix,index,callargs,
                truebeta,as.vector(betahat),value,convcode,timespent,
                writetxt)
}
#tryMAVE <- cmpfun(pre.tryMAVE)
