\name{mult.upgrade}
\alias{mult.upgrade}
\title{ Portfolio selection using multiplicative upgrades }
\description{
  Implement the portfolio selction defined by Hemlbold, Schapire, Singer
  and Warmuth.  The algorihtm is extremely simple but the function
  defined here is not able to exactly reproduced the published results.
}
\usage{
mult.upgrade(x, eta, method)
}
\arguments{
  \item{x}{
    Time series of relative prices
}
\item{eta}{
  Parameter defining the learning rate
}
\item{method}{
  The optimization method, currently only "EG" supported, "exact" is
  planned, but with low priority given the original paper assertion that
  the two approaches were very close in performance.
}
}
\details{
  Straightforward implementation of the multiplicative update
  algorithm.  The complexity is linear in the number of stocks and in
  the number of days making it a very fast algorithm, but with a less
  favorable theoretical bound than Cover's Universal algorithm.
}
\value{
  Return the time series of portfolio weights.
}
\references{
  David P. Helmbold, Robert E. Schapire, Yoram Singer and Manfreg
  K. Warmuth. On-line portfolio selection using multiplicative updates.
  Mathematical Finance, 8(4): 325-347, October 1998.
}
\author{ Marc Delvaux
}

