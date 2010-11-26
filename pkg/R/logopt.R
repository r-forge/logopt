# Code implementing different log optimal portfolio selection
# algorithms, especially linked to universal portfolios
#

require(xts)
require(quadprog)

is.compatible <- function (b, x) {
	# b is either a vector or a matrix
	# x is n (timesteps) * m (assets)
	# we need b = 1 * m or m * 1 or n * m
	if(is.vector(b)) { return(dim(x)[2] == length(b)) }
        if(is.array(b)) { return(all(dim(b) == dim(x))) }
	return(FALSE)
}

normalize <- function (b) {
	if (is.vector(b)) { return (b/sum(b)) }
	else              { return (b/apply(b,1,sum)) }
}

w2x <- function (w) {  # this works for xts because of how lag.xts operates
  	x <- w/lag(w)
  	x[1,] <- w[1,]
  	return(x)
}

# crp and bh are very close, so we implement them as the same procedure
crp_bh <- function (b = NULL, x, bh = FALSE) {
	# bh works on w, crp on x, but otherwise they are similar
  	# - b can be either a vector (constant) or a matrix (weight at each instant in time)
  	#   if b is NULL, we use an uniform vector loading, simple reference
  	# - x is a matrix of price relative, normally an xts
	if (is.null(b)) { b <- rep(1/dim(x)[2],dim(x)[2]) }
  	if(!is.compatible(b,x)) { stop("b and x not compatible in crp(b,x)", Call.=TRUE) } 
  	b <- normalize(b)
	if (bh) { x <- cumprod(x) }
  	if (is.vector(b)) { xp <- x %*% b }
  	else              { xp <- apply(b*x, 1, sum) }
	if (bh) { return (xts(xp, order.by=index(x))) }
	else    { return (xts(cumprod(xp), order.by=index(x)))}
}

crp <- function (b = NULL, x) {
	return (crp_bh(b, x, bh = FALSE))
}

bh <- function (b = NULL, x) {
  	# we accept b as an array, even if this is not really buy and hold
	return (crp_bh(b, x, bh = TRUE))
} 

oracle <- function (x) { # non causal maximum gain
  	xp <- xts(apply(x,1,max), order.by=index(x))
  	return(xts(cumprod(xp), order.by=index(x)))
}

best.asset <- function (x) {
  	xm <- x[,which.max(cumprod(x)[dim(x)[1]])]
  	return(xts(cumprod(xm), order.by=index(x)))
}

worst.asset <- function (x) {
  	xm <- x[,which.min(cumprod(x)[dim(x)[1]])]
  	return(xts(cumprod(xm), order.by=index(x)))
}

best.envelope <- function (x) {
  	wm <- apply(cumprod(x),1,max)
  	return(xts(wm, order.by=index(x)))
}

worst.envelope <- function (x) {
  	wm <- apply(cumprod(x),1,min)
  	return(xts(wm, order.by=index(x)))
}

crp.1d <- function (x, from = 0, to = 1, n = 11) {
  # should have two columns
  if(dim(x)[2] != 2) { stop("x is not a two column series in crp.1d(b,x)", Call.=TRUE) }
  a <- seq(from, to, length.out = n)
  w.1d <- 0 * a
  t <- dim(x)[1]
  for(i in 1:n) {
      w.1d[i] <- crp(c(a[i],1-a[i]),x)[t]
  }
  return(w.1d)
}


round.to.zero <- function (b, do.round, eps) {
	if (do.round) {
		b[abs(b) < eps] <- 0
	}
	return(normalize(b))
}

bcrp.qp <- function (x, clean.up = TRUE, clean.up.eps = 1e-10 ) {
  	# use quadratic programming approximation for VERY fast results in finding best crp
  	# see the semi-log optimal article for background and solve.QP for parameters
  	Dmat <- t(x-1) %*% (x-1)
  	dvec <- apply(x-1,2,sum)
  	lb <- dim(x)[[2]]
  	Amat <- matrix(0,lb,lb+1)
  	Amat[,1] <- -1
  	for (i in 1:lb) { Amat[i,i+1] <- 1 }
  	bvec <- 0 * 1:(lb+1)
  	bvec[1] <- -1
  	b <- solve.QP(Dmat, dvec, Amat, bvec)
	return(round.to.zero(b$solution, clean.up, clean.up.eps))
}

CRPoptrescale <- function (b, x) {
  	b <- exp(b)
  	return(-crp(b,x)[dim(x)[1]])
}

bcrp.optim <- function (x, maxit=20, clean.up = TRUE, clean.up.eps = 1e-10, fast.only = FALSE ) {
  	# try to find a nice BCRP using optim (cam be slow)
  	# optim is unconstrained, and we use a trick to map any value as positive 
  	# then to remap it into the simplex, see CRPoptrescale
	if (dim(x)[1] > dim(x)[2]) {
	  	b0 <- try(bcrp.qp(x))
	}
	else {
		b0 <- rep(1,dim(x)[2])
	}
  	if (inherits(b0,"try-error")) {
		# if we cannot find the best one
		b0 <- rep(0,dim(x)[2])
                # identify best stock and use that as start point
                b0[which.max(apply(x,2,prod))] <- 1
		fast.only = FALSE
  	}
	if (!fast.only) {
	  	solution <- optim(log(b0+clean.up.eps), CRPoptrescale, gr=NULL, method="BFGS", lower=-Inf, upper=Inf,control = list(maxit=maxit), hessian=FALSE, x)
  		b0 <- exp(solution$par)
	}
	return(round.to.zero(b0/sum(b0), clean.up, clean.up.eps))
}

next.simplex.point <- function (a) {
 	# a is the current occupancy, length(a) is the number of "urns"
	# scan to find the first urn that could give a ball
	# push the ball once to the right if possible 
	# if that urn is not empty, bring the rest of the ball to urn[1]
	# returns NULL when done
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

count.grid.points <- function (n, m) {
	# n urns and m balls
	pts <- 1
	if (n < 2) { return(1) }
  	for (i in 1:(n-1)) { pts <- pts * (m+i) / i }
	return(pts)
}

universal.cover <- function (x, n) { # should also return a vector of combined b
	m <- dim(x)[2]
	b <- 0 * 1:m
	b[1] <- n
	npts <- 0
	w <- 0 * x[,1]
	colnames(w) <- c("universal.cover")
	repeat {
		w <- w + crp(b,x)
		npts <- npts + 1
		b <- next.simplex.point(b)
		if (is.null(b)) {
			return(w/npts)
		}
	}
}

# Ishijima methods for uniform and Dirichlet sampling of the simplex
# uniform used the direct method (with sort), not the sequential method with exponent (could be done in fact)
uniform.simplex.sampling <- function (n,m) {
  # n is the number of samples
  # m is the number of dimensions
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

dirichlet.simplex.sampling <- function (n, m, alpha=0.5) {
  # n is the number of samples
  # m is the number of dimensions
  # alpha is the parameter for the gamma
  x <- matrix(rgamma(m * n, alpha), ncol = m, byrow = TRUE)
  sm <- x %*% rep(1, m)
  x/as.vector(sm)
}

universal.cover.random <- function (x, n, method) { # should also return a vector of combined b
	# method is "uniform" or "dirichlet"
	# generation of points in simplex with correct density is based on Ishijima article
	# implementation for dirichlet is however taken from rdirichlet in package 
	m <- dim(x)[2]
	w <- 0 * x[,1]
	colnames(w) <- c("universal.cover")
	if (method == "uniform") { bs <- uniform.simplex.sampling(n,m) }
	if (method == "dirichlet") { bs <- dirichlet.simplex.sampling(n,m) }
	for (i in 1:n) { w <- w + crp(bs[i,],x) }
	return (w/n)
}

mult.upgrade <- function (x, eta, method) { # Multiplicative updates, unable to get reported results
  # method currently supported are "EG" and "chi2"
  # "exact" is more or less planed, but with low priority
  # simple but recursive so needs an explicit loop
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
      b[t,] <- b[t-1,] * ( eta * (x[t-1,] / (b[t-1,] %*% x[t-1,]) - 1) + 1) 
      b[t,] <- b[t,] / sum(b[t,])
    }
    return(b)
  }
  if (method == "exact") {
    print("Method ""exact"" is not currently supported in function mult.upgrade")
    return(NULL)
  }
  return(NULL)
}

switching.portfolio <- function(x, gamma, method) { # Singer switching portfolio approach
  # method is "fixed" or "adaptive"
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
    return(apply(w,1,sum))
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
    return(apply(w,1,sum))
  }
  return(NULL)
}

roll.bcrp <- function (x, start=1, step=1, window=NULL, fast.only=TRUE) {
      m <- dim(x)[2]
      n <- dim(x)[1]
	b <- 0 * x
	b[1:start,] <- 1/m
      i <- start+1
	if(is.null(window)) { window <- length(x) }
      b0 <-  bcrp.optim(x[max(1,i-window):(i-1)], fast.only=fast.only)
	while(i < n) {
		b0 <- bcrp.optim(x[max(1,i-window):(i-1)], fast.only=fast.only)
		b0[is.nan(b0)] <- 1/m
		j <- min(n,i+step)
		bt <- array(rep(b0,j-i+1),dim=c(m,j-i+1))
		b[i:j,] <- t(bt)
		i <- j
	}
	return(b)
} 

wscrp2 <- function (x, start=1, step=1, a=0.99, fast.only=TRUE) {
	br <- roll.bcrp (x, start, step, window=length(x), fast.only=fast.only)
	# should have different choices
      m <- dim(x)[2]
      n <- dim(x)[1]
	b <- 0 * x
	b[1:start,] <- 1/m
      i <- start+1
	b0 <- as.vector(br[i-1,])
	while(i < n) {
		b0 <- as.vector(br[i,]) * (1-a) + b0 * a
		j <- min(n,i+step)
		bt <- array(rep(b0,j-i+1),dim=c(m,j-i+1))
		b[i:j,] <- t(bt)
		i <- j
	}
	return(crp(b,x))
}

wscrp <- function (x, start=1, by=1, alpha=0.99, fast.only=TRUE) {
	# exponential moving average on scrp
      m <- dim(x)[2]
      n <- dim(x)[1]
      b <- 0 * x
      b[1:start,] <- 1/m
      i <- start+1
      b0 <-  bcrp.optim(x[1:(i-1)], fast.only=fast.only)
      while(i < n) {
        b0 <- bcrp.optim(x[1:(i-1)], fast.only=fast.only) * (1-alpha) + b0 * alpha
        b0[is.nan(b0)] <- 1/m
        j <- min(n,i+by)
        bt <- array(rep(b0,j-i+1),dim=c(m,j-i+1))
        b[i:j,] <- t(bt)
        i <- j
      }
      return(crp(b,x))
}

scrp <- function (x, start=1, by=1, fast.only=TRUE) { 
	return(wscrp(x, start=start, by=by, alpha=0, fast.only=fast.only)) 
}


scrp.original <- function (x, k0=1, k=1) {
	# at each t, select the bcrp for up to t-1 as the b for that t
	# for speed, this is only after a start period of K0 points (1/M before)
	# and then every K points
	m <- dim(x)[2]
      n <- dim(x)[1]
	b <- 0 * as.matrix(x)
	b[1:k0,] <- 1/m
      i <- k0+1
	while(i < n) {
		b0 <- bcrp.optim(x[1:(i-1)],fast.only=TRUE)
		j <- min(n,i+k)
		bt <- array(rep(b0,j-i+1),dim=c(m,j-i+1))
		b[i:j,] <- t(bt)
		i <- j
	}
	# there can be rows that are NaN, we replace them with 1/M
	b[is.nan(b)] <- 1/m
	return(crp(b,x))
}

