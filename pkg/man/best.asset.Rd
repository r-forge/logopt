\name{best.asset}
\alias{best.asset}
\title{Time evolution of best asset}
\description{
  Time evolution of the asset with the best terminal price.
}
\usage{
best.asset(x)
}
\arguments{
  \item{x}{
        Time series of relative prices.
}
}
\details{
  Perform a cumprod per column to recover the time series of each asset
  price, find the asset with best terminal price and returns the
  corresponding price time series.  This corresponds to the price time
  series for the best individual asset.
  Contrast with best.envelope that construct a time series of the best price at any time index, irrespective of the asset.
}
\value{
  Time series of the price for the asset with best terminal price.
}

\author{ Marc Delvaux}