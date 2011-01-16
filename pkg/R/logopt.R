# Code implementing different log optimal portfolio selection
# algorithms, especially linked to universal portfolios
#

require(xts)
require(quadprog)
require(FNN)

# check for compatible dimensions
# b is either a vector or a matrix of weights
# x is n (timesteps) * m (assets)
# we need b = 1 * m or m * 1 or n * m
is.compatible <- function (b, x) {
  if(is.vector(b)) { return(dim(x)[2] == length(b)) }
  if(is.array(b)) { return(all(dim(b) == dim(x))) }
  return(FALSE)
}

# sum of weights must be 1 per line
normalize <- function (b) {
  if (is.vector(b)) { return (b/sum(b)) }
  if (is.array(b)) { return (b/apply(b,1,sum)) }
  return(NULL)
}

# take a wealth/price sequence and calculate the wealth/price relative
w2x <- function (w) {
  if (is.xts(w)) {
    x <- w / lag(w)
    x[1,] <- w[1,]
    return(x)
  }
  x <- w
  if (is.vector(w)) {
    n <- length(w)
    x[2:n] <- w[2:n] / w[1:(n-1)]
    return(x)
  }
  if (is.array(w)) {
    n <- dim(w)[1]
    x[2:n,] <- w[2:n,] / w[1:(n-1),]
    return(x)
  }
  return(NULL)
}

# take a price/wealth relative relative and calculate the price/wealth
x2w <- function (x) {
  if (is.xts(x)) { return(cumprod(x)) }
  if (is.array(x)) { return(apply(x,2,cumprod)) }
  if (is.vector(x)) { return(cumprod(x)) }
  return(NULL)
}

# crp and bh are very close, so we implement them as the same procedure
# bh works on w, crp on x, but otherwise they are similar
# - b can be either a vector (constant) or a matrix (weight at each instant in time)
#   if b is NULL, we use an uniform vector loading, simple reference
# - x is a matrix of price relative, normally an xts
crp_bh <- function (x, b = NULL, bh = FALSE) {
  if (is.null(b)) { b <- rep(1/dim(x)[2],dim(x)[2]) }
  if(!is.compatible(b,x)) { stop("b and x not compatible in crp(x,b)", Call.=TRUE) } 
  b <- normalize(b)
  if (bh) { x <- x2w(x) }
  if (is.vector(b)) { xp <- x %*% b }
  else              { xp <- apply(b*x, 1, sum) }
  if (is.xts(x)) { xp <- xts(xp, order.by=index(x)) }
  if (bh) { return(xp) }
  else    { return(x2w(xp)) }
}

crp <- function (x, b = NULL) {
  return (crp_bh(x, b, bh = FALSE))
}

bh <- function (x, b = NULL) {
  return (crp_bh(x, b, bh = TRUE))
} 

oracle <- function (x) { # non causal maximum gain
  if(is.vector(x)) { return(x2w(x)) }
  xp <- apply(x,1,max)
  if (is.xts(x)) { return(xts(x2w(xp), order.by=index(x))) }
  return(x2w(xp))
}

best.asset <- function (x) {
  w <- x2w(x)
  if(is.vector(x)) { return(w) }
  iBest <- which.max(w[dim(x)[1],])
  return(w[,iBest])
}

worst.asset <- function (x) {
  w <- x2w(x)
  if(is.vector(x)) { return(w) }
  iWorst <- which.min(w[dim(x)[1],])
  return(w[,iWorst])
}

best.envelope <- function (x) {
  w <- x2w(x)
  if(is.vector(x)) { return(w) }
  wm <- apply(w,1,max)
  if(is.xts(x)) { return(xts(wm, order.by=index(x))) }
  return(wm)
}

worst.envelope <- function (x) {
  w <- x2w(x)
  if(is.vector(x)) { return(w) }
  wm <- apply(w,1,min)
  if(is.xts(x)) { return(xts(wm, order.by=index(x))) }
  return(wm) 
}

round.to.zero <- function (b, do.round, eps) {
  if (do.round) { b[abs(b) < eps] <- 0 }
  return(normalize(b))
}

# use quadratic programming approximation for fast results in finding best crp
# this is sometimes called semilog
# return the optimal vector of weights
bcrp.qp <- function (x, clean.up = TRUE, clean.up.eps = 1e-10 ) {
  if (is.vector(x)) { return(c(1)) }
  Dmat <- t(x-1) %*% (x-1)
  dvec <- apply(x-1,2,sum)
  lb <- dim(x)[[2]]
  Amat <- matrix(0,lb,lb+1)
  Amat[,1] <- 1
  for (i in 1:lb) { Amat[i,i+1] <- 1 }
  bvec <- 0 * 1:(lb+1)
  bvec[1] <- 1
  b <- solve.QP(Dmat, dvec, Amat, bvec, meq=1)
  bc <- round.to.zero(b$solution, clean.up, clean.up.eps)
  if(any(is.na(bc))) { return(b$solution) }
  else               { return(bc) }
}

# transform axis to insure non negative values, work except that it is not possible to reach 0 values
# alternate approach would use constrained optimization
CRPoptrescale <- function (b, x) {
  b <- exp(b)
  return(-crp(x,b)[dim(x)[1]])
}

# find the optimal CRP weights using optim (can be slow)
# optim is unconstrained, and we use a trick to map any value as positive 
# then to remap it into the simplex, see CRPoptrescale
bcrp.optim <- function (x, maxit=20, clean.up = TRUE, clean.up.eps = 1e-10, fast.only = FALSE ) {
  if(is.vector(x)) { return(c(1)) }
  if (dim(x)[1] > dim(x)[2]) { b0 <- try(bcrp.qp(x)) }
  else                       { b0 <- rep(1,dim(x)[2]); fast.only = FALSE }
  if (inherits(b0,"try-error")) { # bcrp.qp may fail for ill conditioned problems, use best stock as start
    b0 <- rep(0,dim(x)[2])
    b0[which.max(apply(x,2,prod))] <- 1
    fast.only = FALSE
  }
  if (!fast.only) {
    solution <- optim(log(b0+clean.up.eps), CRPoptrescale, gr=NULL, method="BFGS", lower=-Inf, upper=Inf,control = list(maxit=maxit), hessian=FALSE, x)
    b0 <- exp(solution$par)
  }
  return(round.to.zero(normalize(b0), clean.up, clean.up.eps))
}

# use a "urns and balls" approach, a is a vector of balls per urn
# return NULL when done (all balls in the rightmost urn)
next.simplex.point <- function (a) {
  nurns <- length(a)
  for (i in 1:nurns) {
    if (a[i] > 0) {
      if (i == nurns) { return(NULL) }
      else {
        a[i+1] <- 1 + a[i+1]
        a[1] <- a[i] - 1
        if (i != 1) { a[i] <- 0 }
        return(a)
      }
    }
  }
}

# n urns and m balls, i.e. number of simplex points that will be sampled
count.grid.points <- function (n, m) {
  pts <- 1
  if (n < 2) { return(1) }
  for (i in 1:(n-1)) { pts <- pts * (m+i) / i }
  return(pts)
}

# n is the number of sample intervals per dimension, i.e. step is 1/n
universal.cover <- function (x, n) {
  if (is.vector(x)) { return(x2w(x)) }
  m <- dim(x)[2]
  b <- 0 * 1:m
  b[1] <- n
  npts <- 0
  w <- 0 * x[,1]
  repeat {
    w <- w + crp(x, b)
    npts <- npts + 1
    b <- next.simplex.point(b)
    if (is.null(b)) {
      return(w/npts)
    }
  }
}

# Ishijima methods for uniform and Dirichlet sampling of the simplex
# uniform used the direct method (with sort), not the sequential method with exponent (could be done in fact)
# n is the number of samples
# m is the number of dimensions
uniform.simplex.sampling <- function (n,m) {
  if(m==1) { return(runif(n)) }
  x <- array(runif((m-1) * n), dim=c(n,(m-1)))  # prepare for the operation of apply
  if (m > 2) {
    x <- t(apply(x,1,sort))
    y <- apply(x,1,diff)
    if (m>3) { y <- t(y) }
    b <- cbind(x[,1], y, x[,m-1]) 
    return(b)
  }
  return (cbind(x, 1-x))
}

# n is the number of samples
# m is the number of dimensions
# alpha is the parameter for the gamma
dirichlet.simplex.sampling <- function (n, m, alpha=0.5) {
  if(m==1) { return (rgamma(n, alpha)) }
  x <- array(rgamma(m * n, alpha), dim=c(n,m))
  sm <- x %*% rep(1, m)
  x/as.vector(sm)
}

# method is "uniform" or "dirichlet"
# generation of points in simplex with correct density is based on Ishijima article
# implementation for dirichlet is however taken from rdirichlet
# n is the number of sample points
universal.cover.random <- function (x, n, method) { # should also return a vector of combined b
  if(is.vector(x)) { return(w2x(x)) }
  m <- dim(x)[2]
  w <- 0 * x[,1]
  if (method == "uniform") { bs <- uniform.simplex.sampling(n,m) }
  if (method == "dirichlet") { bs <- dirichlet.simplex.sampling(n,m) }
  for (i in 1:n) { w <- w + crp(x, bs[i,]) }
  return (w/n)
}

# multiplicative updates algorithm, does not match published results
# supported methods are: "EG" and "chi2"
# "exact" is planned
# very simple algorithm, but require a loop
mult.upgrade <- function (x, eta, method) {
  if(is.vector(x)) { return(c(1)) }
  if(is.xts(x)) { x <- array(x,dim=dim(x)) }
  b <- 0 * x
  b[1,] <- 1/dim(x)[2]
  if (method == "EG") {
    for (t in 2:dim(x)[1]) {
      b[t,] <- b[t-1,] * exp(eta * x[t-1,] / (b[t-1,] %*% x[t-1,]))
      b[t,] <- b[t,] / sum(b[t,])
    }
    return(b)
  }
  if (method == "chi2") {
    for (t in 2:dim(x)[1]) {
      b[t,] <- b[t-1,] * (eta * (x[t-1,] / (b[t-1,] %*% x[t-1,]) - 1) + 1) 
      b[t,] <- b[t,] / sum(b[t,])
    }
    return(b)
  }
  if (method == "exact") {
    print("Method 'exact' is not currently supported in function mult.upgrade")
    return(NULL)
  }
  return(NULL)
}

# Yoram Singer switching portfolio
# method is "fixed" or "adaptive", "adaptive" does not reproduce published results
switching.portfolio <- function(x, gamma, method) {
  # w[t,i] store the value of asset i after application of x[t,i]
  w <- array(0, dim=dim(x))
  nAssets <- dim(x)[2]
  w[1,] <- 1/nAssets * x[1,]
  if (method == "fixed") {
    for (t in 2:dim(x)[1]) {
        w[t,] <- ((1 - gamma - gamma / (nAssets-1)) *
                  w[t-1,] + 
                  (gamma / (nAssets-1)) * sum(w[t-1,])) * x[t,]
    }
    w <- apply(w,1,sum)
    if(is.xts(x)) { return(xts(w, order.by=index(x))) }
    return(w)
  }
  if (method == "adaptive") {
    # wtt0[t0,i] store the value of the pure strategy starting at t0 before redistribution
    # ghdt stands for gamma hat delta t
    wtt0 <- w
    for (t in 2:dim(x)[1]) {
      past.index <- 1:(t-1)
      ghdt <- 0.5 / (1 + seq(t-1, 1, by = -1))
      out <- wtt0[past.index,] * ghdt # rely on recycling
      if (t == 2) { out.by.asset <- out/(nAssets-1) }
      else        { out.by.asset <- apply(out,2,sum) / (nAssets-1) }
      wtt0[t,] <- -out.by.asset + sum(out.by.asset)
      wtt0[past.index,] <- wtt0[past.index,] - out
      wtt0[1:t,] <- wtt0[1:t,] * rep(x[t,], each=t)
      w[t,] <- apply(wtt0[1:t,],2,sum)
    }
    w <- apply(w,1,sum)
    if(is.xts(x)) { return(xts(w, order.by=index(x))) }
    return(w)
  }
  return(NULL)
}

# roll.bcrp returns the BCRP calculated at a number of points
# and taking into account a window (potentially infinite)
# wl is the window length
# return is a list with
# - the indices of the calculated starts
# - the indices of the calculated ends
# - a matrix of weights
roll.bcrp <- function(x, from=1, by=1, wl=NULL, fast.only=TRUE) {
  # smallish bug, need at least 2 rows for correct operation
  n <- dim(x)[1]
  m <- dim(x)[2]
  from <- max(2,from)
  ends <- seq(from,n,by)
  nw <- length(ends)
  b <- array(1/m,dim=c(nw,m))
  if(is.null(wl)) { wl <- n }
  starts <- pmax(ends-wl+1,1)
  for (i in 1:nw) {
    b[i,] <- bcrp.optim(x[starts[i]:ends[i],], fast.only=fast.only)
  }
  return(list(starts, ends, b))
}

# EMA on the Successive CRP to avoid some instability
wscrp <- function (x, from=1, by=1, alpha=0.99, fast.only=TRUE) {
  m <- dim(x)[2]
  n <- dim(x)[1]
  b <- 0 * x + 1/m
  from <- max(from,2)
  i <- from+1
  # smallish bug, need at least 2 rows for bcrp.optim
  # the problem is that bcrp.optim has been rewritten to assume that a vector is
  # a one column vector, while here it would be a one row vector
  # unfortunately a one row slice becomes a vector and cannot be dsitinguished from
  # a one column vector.  Solution would be to force the slice to be an array of the
  # correct dimension, but this is annoying.  Note that this is only the case for
  # arrays, xts does distinguish between the two cases.
  b0 <- b[1,]
  while(i < n) {
    b0 <- bcrp.optim(x[1:(i-1),], fast.only=fast.only) * (1-alpha) + b0 * alpha
    b0[is.nan(b0)] <- 1/m
    j <- min(n,i+by)
    bt <- array(rep(b0,j-i+1),dim=c(m,j-i+1))
    b[i:j,] <- t(bt)
    i <- j
  }
  return(crp(x, b))
}

scrp <- function (x, from=1, by=1, fast.only=TRUE) { 
  return(wscrp(x, from=from, by=by, alpha=0, fast.only=fast.only)) 
}

# nearest neighbor approach, from Gyorfi, only calculate the porftolio
# themselves at this time, not the weights
# x contains the price relative
# pls is either
# - a scalar, in which case it is the value L in Gyorfi and the pl sequence is 0.02 + 0.05 * (l-1)/(L-1), l in 1:L
# - directly the pl sequence
# ks is either
# - a scalar, in which case it is the value K in Gyorfi and the k sequence is 1:K
# - directly the k sequence
# qkl is the a priori loading on the K*L set of experts, if NULL uniform loading is used
#
nn.gyorfi <- function(x, pls, ks, qkl=NULL) {
  if (is.xts(x)) { x <- array(x,dim=dim(x)) }
  if (is.array(pls)) { L <- length(pls) }
  else               { L <- pls ; pls <- 0.02 + 0.5 / (L-1) * ((1:L)-1) }
  if (is.array(ks)) { K <- length(ks) }
  else              { K <- ks ; ks <- 1:K }
  if(is.null(qkl)) { qkl <- array(1/K/L, dim=c(K,L)) }
  else { # check for compatibility
    if(any(dim(qkl) != c(K,L))) {
      print("qkl loading is not compatible with array of experts")
      return(NULL)
    }
    qkl <- qkl/sum(qkl)
  }
  nSamples <- dim(x)[1]
  nAssets <- dim(x)[2]
  b <- array(1/nAssets,dim=c(K,L,nSamples,nAssets))
  w <- array(0,dim=c(K,L,nSamples))
 # the order of the loop is
  # - k first, to construct the target array
  # - then i (time), to calculate the set of nearest neighbors
  # - then l to extract a subset of the nearest neighbors and optimize
  for (ik in seq_along(ks)) {
    k <- ks[ik]
    # construct the target sequence by column juxtaposition
    for (lag in 0:(k-1)) {
      if (lag == 0) { xnn <- x[1:(nSamples-k+1),] }
      else          { xnn <- cbind(xnn, x[(1+lag):(nSamples-k+1+lag),]) }
    }
    # initial part uses uniform, could extend to more than k
    for (t in (k+2):(nSamples-k-1)) {
      # calculate the set of number of nearest neighbors and their maximum
      # extract the maximum number of nearest neighbor
      ls <- floor((t-k+1) * pls)
      if (max(ls) < 1) { next }
      nnsk <- knnx.index(xnn[1:(t-k),],array(xnn[t-k+1,],dim=c(1,nAssets*k)),max(ls),algorithm="kd_tree")
      for (il in seq_along(ls)) {
        l <- ls[il]
        if (l < 1) { next }
        xcrp <- x[nnsk[1:l]+k,]
        b[ik,il,t+1,] <- bcrp.optim(xcrp,fast.only=TRUE)
        # print(c(ik, k, il, l, t, b[ik,il,t+1,]))
      }
    }
  }
  for (ik in seq_along(ks)) {
    for (il in seq_along(ls)) {
      w[ik,il,] <- crp(x,b[ik,il,,])
    }
  }
  return(list(b,w))
}
