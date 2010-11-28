\name{universal.cover.random}
\alias{universal.cover.random}
\title{ Universal portfolio selection algorithm from Cover }
\description{
  Implement the universal portfolio selection algortihm defined by Cover
  using a sampling approach, needed to avoid exponential complexity in
  number of stocks.
}
\usage{
universal.cover.random(x, n, method)
}
\arguments{
\item{x}{ Time series of relative prices }
\item{n}{ Number of sample points used }
\item{method}{ Probability function controlling the sampling, supported
  at this time are: "uniform" and "dirichlet"
}
}
\details{
  Straightforward implementation of Cover's algorithm, evaluate the
  CRP at the random sample points, return the observed average wealth.
}
\value{
  Return the time series of portfolio wealths.
}
\references{
  Thomas M. Cover. Universal Portfolios.   Mathematical Finance, 1(1): 1-29, January 1991.
}
\author{ Marc Delvaux
}

